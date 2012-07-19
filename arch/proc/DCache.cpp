#include "Processor.h"
#include "sim/log2.h"
#include "sim/config.h"
#include "sim/sampling.h"

#include <cassert>
#include <cstring>
#include <iomanip>
#include <cstdio>
using namespace std;

namespace Simulator
{

Processor::DCache::DCache(const std::string& name, Processor& parent, Clock& clock, Allocator& alloc, FamilyTable& familyTable, RegisterFile& regFile, IMemory& memory, Config& config)
:   Object(name, parent, clock), m_parent(parent),
    m_allocator(alloc), m_familyTable(familyTable), m_regFile(regFile),
    m_memory(memory),

    m_assoc          (config.getValue<size_t>(*this, "Associativity")),
    m_sets           (config.getValue<size_t>(*this, "NumSets")),
    m_wcbsize        (config.getValue<size_t>(*this, "WCBSize")),
    m_lineSize       (config.getValue<size_t>("CacheLineSize")),
    m_selector       (IBankSelector::makeSelector(*this, config.getValue<string>(*this, "BankSelector"), m_sets)),
    m_wcbselect      (IBankSelector::makeSelector(*this, config.getValue<string>(*this, "BankSelector"), m_wcbsize)),
    m_completed      ("b_completed", *this, clock, m_sets * m_assoc),
    m_famflush       ("b_famflush",  *this, clock, m_wcbsize),
    m_incoming       ("b_incoming",  *this, clock, config.getValue<BufferSize>(*this, "IncomingBufferSize")),
    m_outgoing       ("b_outgoing",  *this, clock, config.getValue<BufferSize>(*this, "OutgoingBufferSize")),
    m_numRHits        (0),
    m_numDelayedReads (0),
    m_numEmptyRMisses (0),
    m_numInvalidRMisses(0),
    m_numLoadingRMisses(0),
    m_numHardConflicts(0),
    m_numResolvedConflicts(0),
    m_numWAccesses    (0),
    m_numWHits        (0),
    m_numLoadingWMisses(0),
    m_numStallingRMisses(0),
    m_numStallingWMisses(0),
    m_numSnoops(0),
    m_wcbConflicts   (0),
    m_wcbFlushes      (0),

    p_CompletedReads(*this, "completed-reads", delegate::create<DCache, &Processor::DCache::DoCompletedReads   >(*this) ),
    p_Incoming      (*this, "incoming",        delegate::create<DCache, &Processor::DCache::DoIncomingResponses>(*this) ),
    p_Outgoing      (*this, "outgoing",        delegate::create<DCache, &Processor::DCache::DoOutgoingRequests >(*this) ),
    p_FamFlush      (*this, "FlushWCBInFam",   delegate::create<DCache, &Processor::DCache::DoFamFlush         >(*this) ),

    p_service        (*this, clock, "p_service")
{
    RegisterSampleVariableInObject(m_numRHits, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_numEmptyRMisses, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_numLoadingRMisses, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_numInvalidRMisses, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_numHardConflicts, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_numResolvedConflicts, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_numWHits, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_numLoadingWMisses, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_numStallingRMisses, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_numStallingWMisses, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_wcbConflicts, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_wcbFlushes, SVC_CUMULATIVE);
    
    StorageTraceSet traces;
    m_mcid = m_memory.RegisterClient(*this, p_Outgoing, traces, m_incoming, true);
    p_Outgoing.SetStorageTraces(traces);

    m_completed.Sensitive (p_CompletedReads);
    m_incoming. Sensitive (p_Incoming);
    m_outgoing. Sensitive (p_Outgoing);
    m_famflush. Sensitive (p_FamFlush);
    
    // These things must be powers of two
    if (m_assoc == 0 || !IsPowerOfTwo(m_assoc))
    {
        throw exceptf<InvalidArgumentException>(*this, "DCacheAssociativity = %zd is not a power of two", (size_t)m_assoc);
    }

    if (m_sets == 0 || !IsPowerOfTwo(m_sets))
    {
        throw exceptf<InvalidArgumentException>(*this, "DCacheNumSets = %zd is not a power of two", (size_t)m_sets);
    }
    
    if (m_wcbsize == 0 || !IsPowerOfTwo(m_wcbsize))
    {
        throw exceptf<InvalidArgumentException>(*this, "WCBSize = %zd is not a power of two", (size_t)m_wcbsize);
    }

    if (m_lineSize == 0 || !IsPowerOfTwo(m_lineSize))
    {
        throw exceptf<InvalidArgumentException>(*this, "CacheLineSize = %zd is not a power of two", (size_t)m_lineSize);
    }

    // At least a complete register value has to fit in a line
    if (m_lineSize < 8)
    {
        throw exceptf<InvalidArgumentException>(*this, "CacheLineSize = %zd is less than 8.", (size_t)m_lineSize);
    }

    m_lines.resize(m_sets * m_assoc);
    for (size_t i = 0; i < m_lines.size(); ++i)
    {
        m_lines[i].state  = LINE_EMPTY;
        m_lines[i].data   = new char[m_lineSize];
        m_lines[i].valid  = new bool[m_lineSize];
        m_lines[i].create = false;
    }
    
    m_wcblines.resize(m_wcbsize);
    for (size_t i = 0; i < m_wcblines.size(); ++i)
    {
        m_wcblines[i].free   = true;
        m_wcblines[i].data   = new char[m_lineSize];
        m_wcblines[i].valid  = new bool[m_lineSize];
        std::fill(m_wcblines[i].valid, m_wcblines[i].valid + m_lineSize, false);
       
        
    }
    
    m_wbstate.size   = 0;
    m_wbstate.offset = 0;
}

Processor::DCache::~DCache()
{
    for (size_t i = 0; i < m_lines.size(); ++i)
    {
        delete[] m_lines[i].data;
        delete[] m_lines[i].valid;
    }
    
    for (size_t i = 0; i < m_wcblines.size(); ++i)
    {
        delete[] m_wcblines[i].data;
        delete[] m_wcblines[i].valid;
        
    }
    
    delete m_selector;
    delete m_wcbselect;
}

static std::string valid2str(bool* valid, size_t ms)
{
    std::ostringstream os;
    for (size_t i = 0; i < ms; ++i)
        os << (int)valid[i];
    return os.str();
}


void Processor::DCache::ReadWCB(MemAddr address, Line* line)  
{
    MemAddr tag;
    size_t index, i, offset = address % m_lineSize;
    m_wcbselect->Map((address - offset) / m_lineSize, tag, index);
    
    WCB_Line& wcb_line = m_wcblines[index];
    
    if(!wcb_line.free && (wcb_line.tag == tag))
    {
       
        for (i = 0; i < m_lineSize; ++i)
       {
           if(wcb_line.valid[i])
           {
               COMMIT{
                   line->data[i] = wcb_line.data[i];
                   line->valid[i]= true;
               }
           }
       } 
      
       DebugMemWrite("Cache line update from WCB:%#16llx, index %u, valid %s", (unsigned long long)(address - offset), (unsigned)index, valid2str(wcb_line.valid, m_lineSize).c_str());
    }
    
    return;    
}

bool Processor::DCache::WriteWCB(MemAddr address, MemSize size, void* data, LFID fid)
{
    MemAddr tag;
    size_t index;
    size_t offset = (size_t)(address % m_lineSize);
    m_wcbselect->Map((address - offset) / m_lineSize, tag, index);
    
    WCB_Line& wcb_line = m_wcblines[index];
      
    if(!wcb_line.free && ((wcb_line.fid != fid) || (wcb_line.tag != tag)))
    {
        // flush before combine write data
        if(!FlushWCBLine(index))
        {
            DeadlockWrite("Unable to flush line %u in WCB", (unsigned)index);
            return false;
        }
        COMMIT{ ++m_wcbConflicts;}
                     
    }
    else
        COMMIT{ ++m_numWHits; }
        
    COMMIT {
        memcpy(wcb_line.data + offset, data, (size_t)size);
        std::fill(wcb_line.valid + offset, wcb_line.valid + offset + size, true);
        wcb_line.tag  = tag;
        wcb_line.fid  = fid;
        wcb_line.free = false;
        
    }
    DebugMemWrite("F%u write to WCB line %#16llx, index %u, free %d, size %u, valid %s", (unsigned)wcb_line.fid, (unsigned long long)address, 
                  (unsigned)index, (int)wcb_line.free, (unsigned)size, valid2str(wcb_line.valid, m_lineSize).c_str());
   
    return true;
}

Result Processor::DCache::DoFamFlush()
{
    assert(!m_famflush.Empty());
    LFID   fid     = m_famflush.Front();
    for (vector<WCB_Line>::const_iterator p = m_wcblines.begin(); p != m_wcblines.end(); ++p)
    {
        if(!p->free && p->fid == fid )
        {
           
            if(!FlushWCBLine( p - m_wcblines.begin()))
            {   
              return FAILED;
            }
            return SUCCESS;
        }
    }

    m_famflush.Pop();
    return SUCCESS;
}


bool Processor::DCache::FlushWCBLine(size_t index)
{
    
    
    WCB_Line& wcb_line = m_wcblines[index];    
    assert(!wcb_line.free);
    //put this line into outgoing buffer
    Request request;
    request.write     = true;
    request.address   = m_wcbselect->Unmap(wcb_line.tag,index) * m_lineSize;
    memcpy(request.data.data, wcb_line.data,(size_t)m_lineSize);
    memcpy(request.mask, wcb_line.valid,(size_t)m_lineSize);
    request.fid       =  wcb_line.fid;
        
    if (!m_outgoing.Push(request))
    {
        ++m_numStallingWMisses;
        DeadlockWrite("Unable to push request from wcb line flush to outgoing buffer");
        return false;
    } 
    
    DebugMemWrite("F%u flush WCB line %#16llx, index %u, free %d, size %u, valid %s", (unsigned)wcb_line.fid, (unsigned long long)request.address, 
                  (unsigned)index, (int)wcb_line.free, (unsigned)m_lineSize, valid2str(wcb_line.valid, m_lineSize).c_str());
    
    if (!m_allocator.IncreaseFamilyDependency(wcb_line.fid,FAMDEP_OUTSTANDING_WRITES))
    {
        return false;
    }
    
    COMMIT {           
        std::fill(wcb_line.valid, wcb_line.valid + m_lineSize, false);
        wcb_line.free = true;
        ++m_wcbFlushes;
    }
    
  
    return true;  
}

bool Processor::DCache::FamtoFlush(LFID fid)
{
    for (vector<WCB_Line>::const_iterator p = m_wcblines.begin(); p != m_wcblines.end(); ++p)
    {
       if(!p->free && p->fid == fid )
        {
            return true;
        }
    }
    
    return false;
}

bool Processor::DCache::FlushWCBInFam(LFID fid)
{
   
   assert(fid != INVALID_LFID);
   if(!m_famflush.Push(fid))
   {
       
       DeadlockWrite("Unable to push F%u into flush buffer ", (unsigned)fid);
       return false;    
   }
   return true;
}

Result Processor::DCache::FindLine(MemAddr address, Line* &line, bool check_only)
{
    MemAddr tag;
    size_t setindex;
    m_selector->Map(address / m_lineSize, tag, setindex);
    const size_t  set  = setindex * m_assoc;

    // Find the line
    Line* empty   = NULL;
    Line* replace = NULL;
    for (size_t i = 0; i < m_assoc; ++i)
    {
        line = &m_lines[set + i];
        
        // Invalid lines may not be touched or considered
        if (line->state == LINE_EMPTY)
        {
            // Empty, unused line, remember this one
            empty = line;
        }
        else if (line->tag == tag)
        {
            // The wanted line was in the cache
            return SUCCESS;
        }
        else if (line->state == LINE_FULL && (replace == NULL || line->access < replace->access))
        {
            // The line is available to be replaced and has a lower LRU rating,
            // remember it for replacing
            replace = line;
        }
    }

    // The line could not be found, allocate the empty line or replace an existing line
    line = (empty != NULL) ? empty : replace;
    if (line == NULL)
    {
        // No available line
        if (!check_only)
        {
            DeadlockWrite("Unable to allocate a free cache-line in set %u", (unsigned)(set / m_assoc) );
        }
        return FAILED;
    }

    if (!check_only)
    {
        // Reset the line
        COMMIT
        {
            line->processing = false;
            line->tag        = tag;
            line->waiting    = INVALID_REG;
            std::fill(line->valid, line->valid + m_lineSize, false);
        }
    }

    return DELAYED;
}



Result Processor::DCache::Read(MemAddr address, void* data, MemSize size, RegAddr* reg)
{
    size_t offset = (size_t)(address % m_lineSize);
    if (offset + size > m_lineSize)
    {
        throw exceptf<InvalidArgumentException>(*this, "Read (%#016llx, %zd): Address range crosses over cache line boundary", 
                                                (unsigned long long)address, (size_t)size);
    }

#if MEMSIZE_MAX >= SIZE_MAX
    if (size > SIZE_MAX)
    {
        throw exceptf<InvalidArgumentException>(*this, "Read (%#016llx, %zd): Size argument too big",
                                                (unsigned long long)address, (size_t)size);
    }
#endif

    // Check that we're reading readable memory
    if (!m_parent.CheckPermissions(address, size, IMemory::PERM_READ))
    {
        throw exceptf<SecurityException>(*this, "Read (%#016llx, %zd): Attempting to read from non-readable memory",
                                         (unsigned long long)address, (size_t)size);
    }

    if (!p_service.Invoke())
    {
        DeadlockWrite("Unable to acquire port for D-Cache read access (%#016llx, %zd)",
                      (unsigned long long)address, (size_t)size);

        return FAILED;
    }
    
    Line*  line;
    
    Result result;
    // SUCCESS - A line with the address was found
    // DELAYED - The line with the address was not found, but a line has been allocated
    // FAILED  - No usable line was found at all and could not be allocated
    if ((result = FindLine(address - offset, line, false)) == FAILED)
    {
        // Cache-miss and no free line
        // DeadlockWrite() is done in FindLine
        ++m_numHardConflicts;
        return FAILED;
    }
    
    // Update last line access
    COMMIT{ line->access = GetCycleNo(); }
    
   //Update data from WCB
    ReadWCB(address, line);
    
    // Check if the data that we want is valid in the line.
    // This happens when the line is FULL, or LOADING and has been
    // snooped to (written to from another core) in the mean time.
    
    size_t i;
    for (i = 0; i < size; ++i)
    {
        if (!line->valid[offset + i])
        {
            break;
        }
    }
    
    COMMIT
    {
        if (i == size)
        {
            // Data is entirely in the cache, copy it
            memcpy(data, line->data + offset, (size_t)size);
            
            if(line->state != LINE_LOADING)
                line->state =  LINE_FULL;
           
            ++m_numRHits;
            
            return SUCCESS;            
        }    
        
    }
    
    if(line->state != LINE_LOADING)
    {
        if(line->state == LINE_INVALID)  //hit an invalid line
        {
            ++m_numInvalidRMisses;
            return FAILED;
        }
        // required data is not available, send the request to memory 
        Request request;
        request.write     = false;
        request.address   = address - offset;
        if (!m_outgoing.Push(request))
        {
            ++m_numStallingRMisses;
            DeadlockWrite("Unable to push request to outgoing buffer");
            return FAILED;
        }
    
        // statistics
        COMMIT
        { 
            if (line->state == LINE_EMPTY)
                ++m_numEmptyRMisses;
            else
                ++m_numResolvedConflicts; 
                
        }
    }
    else 
    {
        // Data is loading from memory
        COMMIT{ ++m_numLoadingRMisses; }
    }
        
    // Data is being loaded, add request to the queue
    COMMIT
    {
        line->state = LINE_LOADING;
        if (reg != NULL && reg->valid())
        {
            // We're loading to a valid register, queue it
            RegAddr old   = line->waiting;
            line->waiting = *reg;
            *reg = old;
        }
        else
        {    
            line->create  = true;
        }

        // Statistics:
        ++m_numDelayedReads;
    }
    return DELAYED;
}

Result Processor::DCache::Write(MemAddr address, void* data, MemSize size, LFID fid, TID tid)
{
    assert(fid != INVALID_LFID);
    assert(tid != INVALID_TID);

    size_t offset = (size_t)(address % m_lineSize);
    if (offset + size > m_lineSize)
    {
        throw exceptf<InvalidArgumentException>(*this, "Write (%#016llx, %zd): Address range crosses over cache line boundary", 
                                                (unsigned long long)address, (size_t)size);
    }

#if MEMSIZE_MAX >= SIZE_MAX
    if (size > SIZE_MAX)
    {
        throw exceptf<InvalidArgumentException>(*this, "Write (%#016llx, %zd): Size argument too big",
                                                (unsigned long long)address, (size_t)size);
    }
#endif

    // Check that we're writing writable memory
    if (!m_parent.CheckPermissions(address, size, IMemory::PERM_WRITE))
    {
        throw exceptf<SecurityException>(*this, "Write (%#016llx, %zd): Attempting to write to non-writable memory",
                                         (unsigned long long)address, (size_t)size);
    }

    if (!p_service.Invoke())
    {
        DeadlockWrite("Unable to acquire port for D-Cache write access (%#016llx, %zd)",
                      (unsigned long long)address, (size_t)size);
        return FAILED;
    }
    
    Line* line = NULL;
    Result result = FindLine(address, line, true);
    if (result == SUCCESS)
    {
        assert(line->state != LINE_EMPTY);

        if (line->state == LINE_LOADING || line->state == LINE_INVALID)
        {
            // We cannot write into a loading line or we might violate the
            // sequential semantics of a single thread because pending reads
            // might get the later write's data.
            // We cannot ignore the line either because new reads should get the new
            // data and not the old.
            // We cannot invalidate the line so new reads will generate a new
            // request, because read completion goes on address, and then we would have
            // multiple lines of the same address.
            //
            
            // So for now, just stall the write
            ++m_numLoadingWMisses;
            DeadlockWrite("Unable to write into loading cache line");
            return FAILED;
        }
        else
        {
            // Update the line
            assert(line->state == LINE_FULL);
            COMMIT{ 
                std::copy((char*)data, (char*)data + size, line->data + offset);
                std::fill(line->valid + offset, line->valid + offset + size, true);

                // Statistics
                ++m_numWHits;
               }
           DebugMemWrite("Cache line update from write hit: %#16llx, F%u/T%u", (unsigned long long)address, (unsigned)fid,(unsigned)tid);
        }
    }
    if(!WriteWCB(address, size, data, fid))
    {
        DeadlockWrite("Unable to merge write into WCB");
        return FAILED;
    }

    COMMIT{ ++m_numWAccesses; }

    return DELAYED;

}

bool Processor::DCache::OnMemoryReadCompleted(MemAddr addr, const char* data)
{
    // Check if we have the line and if its loading.
    // This method gets called whenever a memory read completion is put on the
    // bus from memory, so we have to check if we actually need the data.
    Line* line;
    if (FindLine(addr, line, true) == SUCCESS && line->state != LINE_FULL && !line->processing)
    {
        assert(line->state == LINE_LOADING || line->state == LINE_INVALID);

        // Registers are waiting on this data
        COMMIT
        {
            /*        
                      Merge with pending writes because the incoming line
                      will not know about those yet and we don't want inconsistent
                      content in L1.
                      This is kind of a hack; it's feasibility in hardware in a single cycle
                      is questionable.
            */
            char mdata[m_lineSize];
                
            std::copy(data, data + m_lineSize, mdata);

            for (Buffer<Request>::const_iterator p = m_outgoing.begin(); p != m_outgoing.end(); ++p)
            {
                if (p->write && p->address == addr)
                {
                    // This is a write to the same line, merge it
                    line::blit(&mdata[0], p->data.data, p->data.mask, m_lineSize);
                }                    
                DebugMemWrite("Merge outgoing buffer data with load response from 0x%016llx ", (unsigned long long)addr);
                
            }
          
            
            DebugMemWrite("Finished checking data consistency for load response from 0x%016llx ", (unsigned long long)addr);
            
            // Copy the data into the cache line.
            // Mask by valid bytes (don't overwrite already written data).
            line::blitnot(line->data, mdata, line->valid, m_lineSize);
            line::setifnot(line->valid, true, line->valid, m_lineSize);
            
            line->processing = true;
        }
    
              
        // Push the cache-line to the back of the queue
        Response response;
        response.write = false;
        response.cid   = line - &m_lines[0];
        if (!m_incoming.Push(response))
        {
            DeadlockWrite("Unable to push read completion to buffer");
            return false;
        }
    }
    return true;
}

bool Processor::DCache::OnMemoryWriteCompleted(LFID fid)
{
    // Data has been written
    if (fid != INVALID_LFID) // otherwise for DCA
    {
        Response response;
        response.write = true;
        response.fid  =  fid;
        if (!m_incoming.Push(response))
        {
            DeadlockWrite("Unable to push write completion to buffer");
            return false;
        }
    }
    return true;
}

bool Processor::DCache::OnMemorySnooped(MemAddr address, const char* data, const bool* mask)
{
    Line*  line;

    // FIXME: snoops should really either lock the line or access
    // through a different port. Here we cannot (yet) invoke the
    // arbitrator because there is no scaffolding to declare which
    // processes can call OnMemorySnooped via AddProcess().
    /*
    if (!p_service.Invoke())
    {
        DeadlockWrite("Unable to acquire port for D-Cache snoop access (%#016llx, %zd)",
                      (unsigned long long)address, (size_t)data.size);

        return false;
    }
    */

    // Cache coherency: check if we have the same address
    if (FindLine(address, line, true) == SUCCESS)
    {
        COMMIT
        {
            // We do, update the data and mark written bytes as valid
            // Note that we don't have to check against already written data or queued reads
            // because we don't have to guarantee sequential semantics from other cores.
            // This falls within the non-determinism behavior of the architecture.
            line::blit(line->data, data, mask, m_lineSize);
            line::setif(line->valid, true, mask, m_lineSize);

            // Statistics
            ++m_numSnoops;
            
            DebugMemWrite("Cache line update from snoop: 0x%016llx ", (unsigned long long)address);
        }
    }
        
        //Update WCB with dropping valid bytes if matched
    
    MemAddr tag;
    size_t index;
    m_wcbselect->Map(address / m_lineSize, tag, index);
    
    WCB_Line& wcb_line = m_wcblines[index]; 
    if (!wcb_line.free && wcb_line.tag == tag)
    {
        COMMIT{

            line::setif(wcb_line.valid, false, mask, m_lineSize);
            
            // FIXME: this is an optimization, check
            // for rewriting outside of COMMIT block?
            size_t i;
            for (i = 0; i < m_lineSize; ++i)
                if (wcb_line.valid[i])
                    break;
            
            if(i == m_lineSize)
                wcb_line.free = true;
        }
        
        DebugMemWrite("WCB snooping from address 0x%016llx ", (unsigned long long)address);

    }
    
    // Statistics
    COMMIT{ ++m_numSnoops;}
        
    
    return true;
}

bool Processor::DCache::OnMemoryInvalidated(MemAddr address)
{
    COMMIT
    {
        Line* line;
        if (FindLine(address, line, true) == SUCCESS)
        {
            // We have the line, invalidate it
            if (line->state == LINE_FULL) {
                // Full lines are invalidated by clearing them. Simple.
                line->state = LINE_EMPTY;
            } else if (line->state == LINE_LOADING) {
                // The data is being loaded. Invalidate the line and it will get cleaned up
                // when the data is read.
                line->state = LINE_INVALID;
            }
        }
    }
    return true;
}

Result Processor::DCache::DoCompletedReads()
{
    assert(!m_completed.Empty());

    if (!p_service.Invoke())
    {
        DeadlockWrite("Unable to acquire port for D-Cache access in read completion");
        return FAILED;
    }

    // Process a waiting register
    Line& line = m_lines[m_completed.Front()];
    assert(line.state == LINE_LOADING || line.state == LINE_INVALID);
    if (line.waiting.valid())
    {
        WritebackState state = m_wbstate;
        if (state.offset == state.size)
        {
            // Starting a new multi-register write
        
            // Write to register
            if (!m_regFile.p_asyncW.Write(line.waiting))
            {
                DeadlockWrite("Unable to acquire port to write back %s", line.waiting.str().c_str());
                return FAILED;
            }

            // Read request information
            RegValue value;
            if (!m_regFile.ReadRegister(line.waiting, value))
            {
                DeadlockWrite("Unable to read register %s", line.waiting.str().c_str());
                return FAILED;
            }
        
            if (value.m_state == RST_FULL || value.m_memory.size == 0)
            {
                // Rare case: the request info is still in the pipeline, stall!
                DeadlockWrite("Register %s is not yet written for read completion", line.waiting.str().c_str());
                return FAILED;
            }

            if (value.m_state != RST_PENDING && value.m_state != RST_WAITING)
            {
                // We're too fast, wait!
                DeadlockWrite("Memory read completed before register %s was cleared", line.waiting.str().c_str());
                return FAILED;
            }

            // Ignore the request if the family has been killed
            state.value = UnserializeRegister(line.waiting.type, &line.data[value.m_memory.offset], value.m_memory.size);

            if (value.m_memory.sign_extend)
            {
                // Sign-extend the value
                assert(value.m_memory.size < sizeof(Integer));
                int shift = (sizeof(state.value) - value.m_memory.size) * 8;
                state.value = (int64_t)(state.value << shift) >> shift;
            }

            state.fid    = value.m_memory.fid;
            state.addr   = line.waiting;
            state.next   = value.m_memory.next;
            state.offset = 0;

            // Number of registers that we're writing (must be a power of two)
            state.size = (value.m_memory.size + sizeof(Integer) - 1) / sizeof(Integer);
            assert((state.size & (state.size - 1)) == 0);
        }
        else
        {
            // Write to register
            if (!m_regFile.p_asyncW.Write(state.addr))
            {
                DeadlockWrite("Unable to acquire port to write back %s", state.addr.str().c_str());
                return FAILED;
            }
        }

        assert(state.offset < state.size);

        // Write to register file
        RegValue reg;
        reg.m_state = RST_FULL;

#if ARCH_ENDIANNESS == ARCH_BIG_ENDIAN
        // LSB goes in last register
        const Integer data = state.value >> ((state.size - 1 - state.offset) * sizeof(Integer) * 8);
#else
        // LSB goes in first register
        const Integer data = state.value >> (state.offset * sizeof(Integer) * 8);
#endif

        DebugMemWrite("Completed load: %#016llx -> %s",
                      (unsigned long long)data, state.addr.str().c_str());

        switch (state.addr.type) {
            case RT_INTEGER: reg.m_integer       = data; break;
            case RT_FLOAT:   reg.m_float.integer = data; break;
            default: assert(0); // should not be there
        }

        if (!m_regFile.WriteRegister(state.addr, reg, true))
        {
            DeadlockWrite("Unable to write register %s", state.addr.str().c_str());
            return FAILED;
        }
        
        // Update writeback state
        state.offset++;
        state.addr.index++;
        
        if (state.offset == state.size)
        {
            // This operand is now fully written
            if (!m_allocator.DecreaseFamilyDependency(state.fid, FAMDEP_OUTSTANDING_READS))
            {
                DeadlockWrite("Unable to decrement outstanding reads on F%u", (unsigned)state.fid);
                return FAILED;
            }

            COMMIT{ line.waiting = state.next; }
        }
        COMMIT{ m_wbstate = state; }
    }
    else
    {
        if (line.create)
        {
            m_allocator.OnDCachelineLoaded(line.data);
        }
        // We're done with this line.
        // Move the line to the FULL (or EMPTY when invalidated) state.
        COMMIT
        {
            line.state = (line.state == LINE_INVALID) ? LINE_EMPTY : LINE_FULL;
        }
        m_completed.Pop();
    }
    return SUCCESS;
}
        
Result Processor::DCache::DoIncomingResponses()
{
    assert(!m_incoming.Empty());
    const Response& response = m_incoming.Front();
    if (response.write)
    {
        if (!m_allocator.DecreaseFamilyDependency(response.fid,FAMDEP_OUTSTANDING_WRITES))
        {
            DeadlockWrite("Unable to decrease outstanding writes of F%u", (unsigned)response.fid);
            return FAILED;
        }

        DebugMemWrite("F%u completed pending stores", (unsigned)response.fid);

    }
    else
    {
        if (!m_completed.Push(response.cid))
        {
            DeadlockWrite("Unable to buffer read completion to processing buffer");
            return FAILED;
        }
    }
    m_incoming.Pop();
    return SUCCESS;
}

Result Processor::DCache::DoOutgoingRequests()
{
    assert(!m_outgoing.Empty());
    const Request& request = m_outgoing.Front();

    assert(request.address % m_lineSize == 0);
    
    if (request.write)
    {
        if (!m_memory.Write(m_mcid, request.address, request.data, request.fid))
        {
            DeadlockWrite("Unable to send write to 0x%016llx to memory", (unsigned long long)request.address);
            return FAILED;
        }
    }
    else
    {
        if (!m_memory.Read(m_mcid, request.address))
        {
            DeadlockWrite("Unable to send read to 0x%016llx to memory", (unsigned long long)request.address);
            return FAILED;
        }
    }

    DebugMemWrite("F%d queued outgoing %s request for %.*llx",
                  (request.write ? (int)request.fid : -1), (request.write ? "store" : "load"),
                  (int)(sizeof(MemAddr)*2), (unsigned long long)request.address);

    m_outgoing.Pop();
    return SUCCESS;
}

void Processor::DCache::Cmd_Info(std::ostream& out, const std::vector<std::string>& /*arguments*/) const
{
    out <<
    "The Data Cache stores data from memory that has been used in loads and stores\n"
    "for faster access. Compared to a traditional cache, this D-Cache is extended\n"
    "with several fields to support the multiple threads and asynchronous operation.\n\n"
    "Supported operations:\n"
    "- inspect <component>\n"
    "  Display global information such as hit-rate and configuration.\n"
    "- inspect <component> buffers\n" 
    "  Reads and display the outgoing request buffer.\n"
    "- inspect <component> wcb\n" 
    "  Reads and display used lines in Write Combine Buffer.\n"
    "- inspect <component> lines\n"
    "  Reads and displays the cache-lines.\n";
}

void Processor::DCache::Cmd_Read(std::ostream& out, const std::vector<std::string>& arguments) const
{
    if (arguments.empty())
    {
        out << "Cache type:          ";
        if (m_assoc == 1) {
            out << "Direct mapped" << endl;
        } else if (m_assoc == m_lines.size()) {
            out << "Fully associative" << endl;
        } else {
            out << dec << m_assoc << "-way set associative" << endl;
        }
        
        out << "L1 bank mapping:     " << m_selector->GetName() << endl
            << "Cache size:          " << dec << (m_lineSize * m_lines.size()) << " bytes" << endl
            << "Cache line size:     " << dec << m_lineSize << " bytes" << endl
            << endl;

        uint64_t numRAccesses = m_numRHits + m_numDelayedReads;

        uint64_t numRRqst = m_numEmptyRMisses + m_numResolvedConflicts;
        uint64_t numWRqst = m_wcbFlushes;
        uint64_t numRqst  = numRRqst + numWRqst;

        uint64_t numRStalls = m_numHardConflicts + m_numInvalidRMisses + m_numStallingRMisses;
        uint64_t numWStalls = m_numLoadingWMisses + m_numStallingWMisses;
        uint64_t numStalls  = numRStalls + numWStalls;

        if (numRAccesses == 0 && m_numWAccesses == 0 && numStalls == 0)
            out << "No accesses so far, cannot provide statistical data." << endl;
        else
        {
            out << "***********************************************************" << endl
                << "                      Summary                              " << endl
                << "***********************************************************" << endl
                << endl << dec
                << "Number of read requests from client:  " << numRAccesses << endl
                << "Number of write requests from client: " << m_numWAccesses << endl
                << "Number of requests to upstream:       " << numRqst      << endl
                << "Number of snoops from siblings:       " << m_numSnoops  << endl
                << "Number of stalled cycles:             " << numStalls    << endl
                << endl;
                
#define PRINTVAL(X, q) dec << (X) << " (" << setprecision(2) << fixed << (X) * q << "%)"
            
            float r_factor = 100.0f / numRAccesses;
            out << "***********************************************************" << endl
                << "                      Cache reads                          " << endl
                << "***********************************************************" << endl
                << endl
                << "Number of read requests from client:                " << numRAccesses << endl
                << "Read hits:                                          " << PRINTVAL(m_numRHits, r_factor) << endl
                << "Read misses:                                        " << PRINTVAL(m_numDelayedReads, r_factor) << endl
                << "Breakdown of read misses:" << endl                  
                << "- to an empty line:                                 " << PRINTVAL(m_numEmptyRMisses, r_factor) << endl
                << "- to a loading line with same tag:                  " << PRINTVAL(m_numLoadingRMisses, r_factor) << endl
                << "- to a reusable line with different tag (conflict): " << PRINTVAL(m_numResolvedConflicts, r_factor) << endl
                << "(percentages relative to " << numRAccesses << " read requests)" << endl
                << endl;
            
            float w_factor = 100.0f / m_numWAccesses;
            out << "***********************************************************" << endl
                << "                      Cache writes                         " << endl
                << "***********************************************************" << endl
                << endl
                << "Number of write requests from client:                           " << m_numWAccesses << endl
                << "Breakdown of writes:" << endl
                << "- to a loaded line with same tag:                               " << PRINTVAL(m_numWHits, w_factor) << endl
                << "- to a wcb line with different tag:                             " << PRINTVAL( m_wcbConflicts, w_factor) << endl
                << "(percentages relative to " << m_numWAccesses << " write requests)" << endl
                << endl;
            
            float q_factor = 100.0f / numRqst;                
            out << "***********************************************************" << endl
                << "                      Requests to upstream                 " << endl
                << "***********************************************************" << endl
                << endl
                << "Number of requests to upstream: " << numRqst  << endl
                << "Read requests:                  " << PRINTVAL(numRRqst, q_factor) << endl
                << "Write requests:                 " << PRINTVAL(numWRqst, q_factor) << endl
                << "(percentages relative to " << numRqst << " requests)" << endl
                << endl;
                
                
            if (numStalls != 0)
            {
                float s_factor = 100.f / numStalls;   
                out << "***********************************************************" << endl
                    << "                      Stall cycles                         " << endl
                    << "***********************************************************" << endl
                    << endl
                    << "Number of stall cycles:               " << numStalls << endl
                    << "Read-related stalls:                  " << PRINTVAL(numRStalls, s_factor) << endl 
                    << "Write-related stalls:                 " << PRINTVAL(numWStalls, s_factor) << endl
                    << "Breakdown of read-related stalls:" << endl
                    << "- read conflict to non-reusable line: " << PRINTVAL(m_numHardConflicts, s_factor) << endl
                    << "- read to invalidated line:           " << PRINTVAL(m_numInvalidRMisses, s_factor) << endl
                    << "- unable to send request upstream:    " << PRINTVAL(m_numStallingRMisses, s_factor) << endl
                    << "Breakdown of write-related stalls:" << endl
                    << "- writes to loading line:             " << PRINTVAL(m_numLoadingWMisses, s_factor) << endl
                    << "- unable to send request upstream:    " << PRINTVAL(m_numStallingWMisses, s_factor) << endl
                    << "(percentages relative to " << numStalls << " stall cycles)" << endl
                    << endl;
            }
             
        }
        return;
    }
    else if (arguments[0] == "buffers")
    {
        out << endl << "Outgoing requests:" << endl << endl
            << "      Address      | Type  | Value (writes)" << endl
            << "-------------------+-------+-------------------------" << endl;
        for (Buffer<Request>::const_iterator p = m_outgoing.begin(); p != m_outgoing.end(); ++p)
        {
            out << hex << "0x" << setw(16) << setfill('0') << p->address << " | "
                << (p->write ? "Write" : "Read ") << " |";
            if (p->write)
            {
                out << hex << setfill('0');
                static const int BYTES_PER_LINE = 16;
                for (size_t y = 0; y < m_lineSize; y += BYTES_PER_LINE)
                {
                    for (size_t x = y; x < y + BYTES_PER_LINE; ++x)
                    {
                        out << " ";
                        if (p->mask[x]) {
                            out<< setw(2) << (unsigned)(unsigned char)p->data.data[x];
                        }
                        else {
                            out << "--";
                        }
                    }             
                    
                    if (y + BYTES_PER_LINE < m_lineSize) {
                        // This was not yet the last line
                        out << endl << "                   |       |";
                    }
                }
                out << endl << "-------------------+------+-------+------------------------------------------------" << endl;
            }
            out << dec << endl;
        }
        return;
    }
    else if (arguments[0] == "wcb")
    {
        out << endl << "Write Combine Buffer line in use:" << endl << endl
        << "Free | Set |       Address      |  FID  |                       Data                     " << endl
        << "-----+-----+--------------------+-------+------------------------------------------------" << endl;
        for (size_t j = 0; j < m_wcblines.size(); ++j)
        {
            const WCB_Line& wcb_line = m_wcblines[j];
            if (!wcb_line.free)
            {
                out <<setw(4) << setfill(' ')<< (wcb_line.free?"T":"F") << " | " 
                << setw(3) << setfill(' ')<< dec << right << j <<" | " 
                << hex << "0x" << setw(16) << setfill('0') << m_wcbselect->Unmap(wcb_line.tag, j) * m_lineSize << " | "
                << dec << setw(5) << right << setfill(' ') << wcb_line.fid << " |";
                out << hex << setfill('0');
                static const int BYTES_PER_LINE = 16;
                for (size_t y = 0; y < m_lineSize; y += BYTES_PER_LINE)
                {
                    for (size_t x = y; x < y + BYTES_PER_LINE; ++x) {
                        out << " ";
                        if (wcb_line.valid[x]) {
                            out << setw(2) << (unsigned)(unsigned char)wcb_line.data[x];
                        } else {
                           out << "--";
                        }
                    }             
                                    
                    if (y + BYTES_PER_LINE < m_lineSize) {
                        // This was not yet the last line
                        out << endl << "     |     |                    |       |";
                    }
                }
                out << endl << "-----+-----+--------------------+-------+------------------------------------------------" << endl;
            }
            
        }
        return;
    }

    out << "Set |       Address       |                       Data                      | Waiting Registers" << endl;
    out << "----+---------------------+-------------------------------------------------+-------------------" << endl;
    for (size_t i = 0; i < m_lines.size(); ++i)
    {
        const size_t set = i / m_assoc;
        const Line& line = m_lines[i];

        if (i % m_assoc == 0) {
            out << setw(3) << setfill(' ') << dec << right << set;
        } else {
            out << "   ";
        }

        if (line.state == LINE_EMPTY) {
            out << " |                     |                                                 |";
        } else {
            out << " | "
                << hex << "0x" << setw(16) << setfill('0') << m_selector->Unmap(line.tag, set) * m_lineSize;
            
            switch (line.state)
            {
                case LINE_LOADING: out << "L"; break;
                case LINE_INVALID: out << "I"; break;
                default: out << " ";
            }
            out << " |";

            // Get the waiting registers
            std::vector<RegAddr> waiting;
            RegAddr reg = line.waiting;
            while (reg != INVALID_REG)
            {
                waiting.push_back(reg);
                RegValue value;
                m_regFile.ReadRegister(reg, value, true);
                
                if (value.m_state == RST_FULL || value.m_memory.size == 0)
                {
                    // Rare case: the request info is still in the pipeline, stall!
                    waiting.push_back(INVALID_REG);
                    break;
                }

                if (value.m_state != RST_PENDING && value.m_state != RST_WAITING)
                {
                    // We're too fast, wait!
                    waiting.push_back(INVALID_REG);
                    break;
                }

                reg = value.m_memory.next;
            }

            // Print the data
            out << hex << setfill('0');
            static const int BYTES_PER_LINE = 16;
            const int nLines = (m_lineSize + BYTES_PER_LINE + 1) / BYTES_PER_LINE;
            const int nWaitingPerLine = (waiting.size() + nLines + 1) / nLines;
            for (size_t y = 0; y < m_lineSize; y += BYTES_PER_LINE)
            {
                for (size_t x = y; x < y + BYTES_PER_LINE; ++x) {
                    out << " ";
                    if (line.valid[x]) {
                        out << setw(2) << (unsigned)(unsigned char)line.data[x];
                    } else {
                        out << "  ";
                    }
                }

                out << " |";
                
                // Print waiting registers for this line
                for (int w = 0; w < nWaitingPerLine; ++w)
                {
                    size_t index = y / BYTES_PER_LINE * nWaitingPerLine + w;
                    if (index < waiting.size())
                    {
                        RegAddr reg = waiting[index];
                        out << " ";
                        if (reg == INVALID_REG) out << "[...]"; // And possibly others
                        else out << reg.str();
                    }
                }
                
                if (y + BYTES_PER_LINE < m_lineSize) {
                    // This was not yet the last line
                    out << endl << "    |                     |";
                }
            }
        }
        out << endl;
        out << ((i + 1) % m_assoc == 0 ? "----" : "    ");
        out << "+---------------------+-------------------------------------------------+-------------" << endl;
    }

}

}
