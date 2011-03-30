/*
mgsim: Microgrid Simulator
Copyright (C) 2006,2007,2008,2009,2010,2011  The Microgrid Project.

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Library General Public
License as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Library General Public License for more details.

You should have received a copy of the GNU Library General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
*/
#include "Cache.h"
#include "RootDirectory.h"
#include "../config.h"
#include "../sampling.h"
#include <cassert>
#include <cstring>
using namespace std;

namespace Simulator
{

template <typename T>
static bool IsPowerOfTwo(const T& x)
{
    return (x & (x - 1)) == 0;
}

void COMA::RegisterClient(PSize pid, IMemoryCallback& callback, const Process* processes[])
{
    // Forward the registration to the cache associated with the processor
    m_caches[pid / m_numProcsPerCache]->RegisterClient(pid, callback, processes);
}

void COMA::UnregisterClient(PSize pid)
{
    // Forward the unregistration to the cache associated with the processor
    m_caches[pid / m_numProcsPerCache]->UnregisterClient(pid);
}

bool COMA::Read(PSize pid, MemAddr address, MemSize size)
{
    COMMIT
    {
        m_nreads++;
        m_nread_bytes += size;
    }
    // Forward the read to the cache associated with the callback
    return m_caches[pid / m_numProcsPerCache]->Read(pid, address, size);
}

bool COMA::Write(PSize pid, MemAddr address, const void* data, MemSize size, TID tid)
{
    // Until the write protocol is figured out, do magic coherence!
    COMMIT
    {
        m_nwrites++;
        m_nwrite_bytes += size;
    }
    // Forward the write to the cache associated with the callback
    return m_caches[pid / m_numProcsPerCache]->Write(pid, address, data, size, tid);
}

void COMA::Reserve(MemAddr address, MemSize size, int perm)
{
    return VirtualMemory::Reserve(address, size, perm);
}

void COMA::Unreserve(MemAddr address)
{
    return VirtualMemory::Unreserve(address);
}

bool COMA::Allocate(MemSize size, int perm, MemAddr& address)
{
    return VirtualMemory::Allocate(size, perm, address);
}

void COMA::Read(MemAddr address, void* data, MemSize size)
{
    return VirtualMemory::Read(address, data, size);
}

void COMA::Write(MemAddr address, const void* data, MemSize size)
{
	return VirtualMemory::Write(address, data, size);
}

bool COMA::CheckPermissions(MemAddr address, MemSize size, int access) const
{
	return VirtualMemory::CheckPermissions(address, size, access);
}

COMA::COMA(const std::string& name, Simulator::Object& parent, Clock& clock, const Config& config) :
    // Note that the COMA class is just a container for caches and directories.
    // It has no processes of its own.
    Simulator::Object(name, parent, clock),
    m_numProcsPerCache(std::max<size_t>(1, config.getValue<size_t>("NumProcessorsPerCache", 4))),
    m_numCachesPerDir (std::max<size_t>(1, config.getValue<size_t>("NumCachesPerDirectory", 4))),
    
    m_nreads(0), m_nwrites(0), m_nread_bytes(0), m_nwrite_bytes(0)
{

    RegisterSampleVariableInObject(m_nreads, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_nread_bytes, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_nwrites, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_nwrite_bytes, SVC_CUMULATIVE);

    // Create the caches
    size_t numProcs = config.getValue<size_t>("NumProcessors", 1);
    m_caches.resize( (numProcs + m_numProcsPerCache - 1) / m_numProcsPerCache );
    for (size_t i = 0; i < m_caches.size(); ++i)
    {
        stringstream name;
        name << "cache" << i;
        m_caches[i] = new Cache(name.str(), *this, clock, i, m_caches.size(), config);
    }
    
    // Create the directories
    m_directories.resize( (m_caches.size() + m_numCachesPerDir - 1) / m_numCachesPerDir );
    for (size_t i = 0; i < m_directories.size(); ++i)
    {
        CacheID firstCache = i * m_numCachesPerDir;
        CacheID lastCache  = std::min(firstCache + m_numCachesPerDir, m_caches.size()) - 1;
        
        stringstream name;
        name << "dir" << i;
        m_directories[i] = new Directory(name.str(), *this, clock, firstCache, lastCache, config);
    }
    
    // Create the root directories
    m_roots.resize( std::max<size_t>(1, config.getValue<size_t>("NumRootDirectories", 1)) );
    if (!IsPowerOfTwo(m_roots.size()))
    {
        throw InvalidArgumentException("NumRootDirectories is not a power of two");
    }
    
    for (size_t i = 0; i < m_roots.size(); ++i)
    {
        stringstream name;
        name << "rootdir" << i;
        m_roots[i] = new RootDirectory(name.str(), *this, clock, *this, m_caches.size(), i, m_roots.size(), config);
    }
    
    // Initialize the caches
    for (size_t i = 0; i < m_caches.size(); ++i)
    {
        DirectoryBottom* dir = &m_directories[i / m_numCachesPerDir]->m_bottom;
        const bool first = (i % m_numCachesPerDir == 0);
        const bool last  = (i % m_numCachesPerDir == m_numCachesPerDir - 1) || (i == m_caches.size() - 1);
        m_caches[i]->Initialize(
            first ? dir : static_cast<Node*>(m_caches[i-1]),
            last  ? dir : static_cast<Node*>(m_caches[i+1]) );
    }
    
    // Connect the directories to the cache rings
    for (size_t i = 0; i < m_directories.size(); ++i)
    {
        m_directories[i]->m_bottom.Initialize(
            m_caches[std::min(i * m_numCachesPerDir + m_numCachesPerDir, m_caches.size()) - 1],
            m_caches[i * m_numCachesPerDir] );
    }

    //
    // Figure out the layout of the top-level ring
    //
    std::vector<Node*> nodes(m_roots.size() + m_directories.size(), NULL);

    // First place root directories in their place in the ring.
    for (size_t i = 0; i < m_roots.size(); ++i)
    {
        // Do an even (as possible) distribution
        size_t pos = i * m_directories.size() / m_roots.size() + i;
        
        // In case we map to an already used spot (for uneven distributions), find the next free spot
        while (nodes[pos] != NULL) pos = (pos + 1) % nodes.size();
        nodes[pos] = m_roots[i];
    }
    
    // Then fill up the gaps with the directories
    for (size_t p = 0, i = 0; i < m_directories.size(); ++i, ++p)
    {
        while (nodes[p] != NULL) ++p;
        nodes[p] = &m_directories[i]->m_top;
    }
    
    // Now connect everything on the top-level ring
    for (size_t i = 0; i < nodes.size(); ++i)
    {
        nodes[i]->Initialize(
            nodes[(i == 0 ? nodes.size() : i) - 1],
            nodes[(i + 1) % nodes.size()] );
    }
}

COMA::~COMA()
{
    for (size_t i = 0; i < m_caches.size(); ++i)
    {
        delete m_caches[i];
    }
    
    for (size_t i = 0; i < m_directories.size(); ++i)
    {
        delete m_directories[i];
    }

    for (size_t i = 0; i < m_roots.size(); ++i)
    {
        delete m_roots[i];
    }
}

void COMA::GetMemoryStatistics(uint64_t& nreads, uint64_t& nwrites, uint64_t& nread_bytes, uint64_t& nwrite_bytes, uint64_t& nreads_ext, uint64_t& nwrites_ext) const
{
    nreads = m_nreads;
    nwrites = m_nwrites;
    nread_bytes = m_nread_bytes;
    nwrite_bytes = m_nwrite_bytes;

    uint64_t nre = 0, nwe = 0;
    for (size_t i = 0; i < m_roots.size(); ++i)
    {
        m_roots[i]->GetMemoryStatistics(nre, nwe);
        nreads_ext += nre;
        nwrites_ext += nwe;
    }
}

void COMA::Cmd_Help(ostream& out, const vector<string>& /*arguments*/) const
{
    out <<
    "The COMA Memory represents a hierarchical ring-based network of caches where each\n"
    "cache services several processors. Rings of caches are connected via directories\n"
    "to higher-level rings. One or more root directories at the top provide access to\n"
    "to off-chip storage."
    "Supported operations:\n"
    "- info <component>\n"
    "  Displays the currently reserved and allocated memory ranges\n\n"
    "- read <component> <start> <size>\n"
    "  Reads the specified number of bytes of raw data from memory from the\n"
    "  specified address\n\n"
    "- line <component> <address>\n"
    "  Finds the specified line in the system and prints its distributed state\n"
    "- trace <component> <address> [clear]\n"
    "  Sets or clears tracing for the specified address\n";
}

void COMA::Cmd_Line(ostream& out, const vector<string>& arguments) const
{
    // Parse argument
    MemAddr address = 0;
    char* endptr = NULL;
    if (arguments.size() == 1)
    {
        address = (MemAddr)strtoull( arguments[0].c_str(), &endptr, 0 );
    }

    if (arguments.size() != 1 || *endptr != '\0')
    {
        out << "Usage: line <mem> <address>" << endl;
        return;
    }

    // Check the root directories
    bool printed = false;
    for (std::vector<RootDirectory*>::const_iterator p = m_roots.begin(); p != m_roots.end(); ++p)
    {
        const RootDirectory::Line* line = static_cast<const RootDirectory*>(*p)->FindLine(address);
        if (line != NULL)
        {
            const char* state = (line->state == RootDirectory::LINE_LOADING) ? "loading" : "loaded";
            out << (*p)->GetFQN() << ": " << state << endl;
            printed = true;
        }
    }
    if (printed) out << endl;

    // Check the directories
    printed = false;
    for (std::vector<Directory*>::const_iterator p = m_directories.begin(); p != m_directories.end(); ++p)
    {
        const Directory::Line* line = static_cast<const Directory*>(*p)->FindLine(address);
        if (line != NULL)
        {
            out << (*p)->GetFQN() << ": present" << endl;
            printed = true;
        }
    }
    if (printed) out << endl;
    
    // Check the caches
    printed = false;
    for (std::vector<Cache*>::const_iterator p = m_caches.begin(); p != m_caches.end(); ++p)
    {
        const Cache::Line* line = static_cast<const Cache*>(*p)->FindLine(address);
        if (line != NULL)
        {
            const char* state = (line->state == Cache::LINE_LOADING) ? "loading" : "loaded";
            out << (*p)->GetFQN() << ": " << state << ", " << line->tokens << " tokens" << endl;
            printed = true;
        }
    }
    if (printed) out << endl;
}

void COMA::Cmd_Trace(ostream& out, const vector<string>& arguments)
{
    // Parse argument
    MemAddr address;
    char* endptr = NULL;
    if (!arguments.empty())
    {
        address = (MemAddr)strtoull( arguments[0].c_str(), &endptr, 0 );
    }

    if (arguments.empty() || *endptr != '\0')
    {
        out << "Usage: trace <mem> <address> [clear]" << endl;
        return;
    }

    if (arguments.size() > 1 && arguments[1] == "clear")
    {
        m_traces.erase(address);
        out << "Disabled tracing of address 0x" << hex << address << endl;
    }
    else
    {
        m_traces.insert(address);
        out << "Enabled tracing of address 0x" << hex << address << endl;
    }
}

}
