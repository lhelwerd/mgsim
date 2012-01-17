#ifndef COMA_COMA_H
#define COMA_COMA_H

#include "arch/Memory.h"
#include "arch/VirtualMemory.h"
#include "arch/BankSelector.h"
#include "sim/inspect.h"
#include "mem/DDR.h"
#include <queue>
#include <set>

class Config;
class ComponentModelRegistry;

namespace Simulator
{

class COMA : public Object, public IMemoryAdmin, public VirtualMemory, public Inspect::Interface<Inspect::Line|Inspect::Trace>
{
public:
    class Node;
    class DirectoryTop;
    class DirectoryBottom;
    class Directory;
    class RootDirectory;
    class Cache;
    
    // A simple base class for all COMA objects. It keeps track of what
    // COMA memory it's in.
    class Object : public virtual Simulator::Object
    {
    protected:
        COMA& m_parent;
        
    public:
        Object(const std::string& name, COMA& parent)
            : Simulator::Object(name, parent), m_parent(parent) {}
        virtual ~Object() {}
    };

private:    
    typedef std::set<MemAddr> TraceMap;
    typedef size_t            CacheID;
    
    ComponentModelRegistry&     m_registry;
    size_t                      m_numClientsPerCache;
    size_t                      m_numCachesPerDir;
    size_t                      m_numClients;
    Config&                     m_config;
    IBankSelector*              m_selector;           ///< Mapping of line addresses to set indexes
    std::vector<Cache*>         m_caches;             ///< List of caches
    std::vector<Directory*>     m_directories;        ///< List of directories
    std::vector<RootDirectory*> m_roots;              ///< List of root directories
    TraceMap                    m_traces;             ///< Active traces
    DDRChannelRegistry          m_ddr;                ///< List of DDR channels
    
    std::vector<std::pair<Cache*,MCID> > m_clientMap; ///< Mapping of MCID to caches

    uint64_t                    m_nreads, m_nwrites, m_nread_bytes, m_nwrite_bytes;
    
    void ConfigureTopRing();
    
    unsigned int GetTotalTokens() const {
        // One token per cache
        return m_caches.size();
    }
    
    void Initialize();
    
public:
    COMA(const std::string& name, Simulator::Object& parent, Clock& clock, Config& config);
    ~COMA();

    const TraceMap& GetTraces() const { return m_traces; }

    IBankSelector& GetBankSelector() const { return *m_selector; }
    
    size_t GetLineSize() const;
    size_t GetNumActiveCachePeers() const {return (m_caches.size() > m_numCachesPerDir) ? m_numCachesPerDir : m_caches.size(); }
    size_t GetNumClientsPerCache() const { return m_numClientsPerCache; }    
    size_t GetNumCachesPerDirectory() const { return m_numCachesPerDir; }
    size_t GetNumCaches() const { return m_caches.size(); }
    size_t GetNumDirectories() const { return m_directories.size(); }
    size_t GetNumRootDirectories() const { return m_roots.size(); }
    size_t GetNumCacheSets() const;
    size_t GetCacheAssociativity() const;
    size_t GetDirectoryAssociativity() const;
    
    // IMemory
    MCID RegisterClient(IMemoryCallback& callback, Process& process, StorageTraceSet& traces, Storage& storage, bool grouped);
    void UnregisterClient(MCID id);
    bool Read (MCID id, MemAddr address, MemSize /* unused, remove! */);
    bool Write(MCID id, MemAddr address, const void* data, MemSize /* unused, remove! */, LFID fid, const bool* mask, bool consistency);
    bool CheckPermissions(MemAddr address, MemSize size, int access) const;

    void GetMemoryStatistics(uint64_t& nreads, uint64_t& nwrites, 
                             uint64_t& nread_bytes, uint64_t& nwrite_bytes,
                             uint64_t& nreads_ext, uint64_t& nwrites_ext) const;

    void Cmd_Info (std::ostream& out, const std::vector<std::string>& arguments) const;
    void Cmd_Line (std::ostream& out, const std::vector<std::string>& arguments) const;
    void Cmd_Trace(std::ostream& out, const std::vector<std::string>& arguments);

    // IMemoryAdmin
    void Reserve(MemAddr address, MemSize size, ProcessID pid, int perm);
    void Unreserve(MemAddr address, MemSize size);
    void UnreserveAll(ProcessID pid);

    void Read (MemAddr address, void* data, MemSize size);
    void Write(MemAddr address, const void* data, MemSize size);
};

}
#endif
