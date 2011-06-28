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
#ifndef BANKEDMEMORY_H
#define BANKEDMEMORY_H

#include "BankSelector.h"
#include "arch/Memory.h"
#include "arch/VirtualMemory.h"
#include "sim/inspect.h"
#include <queue>
#include <set>

class Config;
class ComponentModelRegistry;

namespace Simulator
{

class ArbitratedWriteFunction;

class BankedMemory : public Object, public IMemoryAdmin, public VirtualMemory
{
    struct ClientInfo;
    struct Request;
    class Bank;

    std::pair<CycleNo, CycleNo> GetMessageDelay(size_t body_size) const;
    CycleNo                     GetMemoryDelay (size_t data_size) const;

    // IMemory
    void Reserve(MemAddr address, MemSize size, int perm);
    void Unreserve(MemAddr address);
    MCID RegisterClient(IMemoryCallback& callback, Process& process, StorageTraceSet& traces, Storage& storage, bool /*ignored*/);
    void UnregisterClient(MCID id);
    bool Read (MCID id, MemAddr address, MemSize size);
    bool Write(MCID id, MemAddr address, const void* data, MemSize size, TID tid);
	bool CheckPermissions(MemAddr address, MemSize size, int access) const;

    // IMemoryAdmin
    bool Allocate(MemSize size, int perm, MemAddr& address);
    void Read (MemAddr address, void* data, MemSize size);
    void Write(MemAddr address, const void* data, MemSize size);

    void GetMemoryStatistics(uint64_t& nreads, uint64_t& nwrites, 
                             uint64_t& nread_bytes, uint64_t& nwrite_bytes,
                             uint64_t& nreads_ext, uint64_t& nwrites_ext) const
    {
        nreads = m_nreads;
        nwrites = m_nwrites;
        nread_bytes = m_nread_bytes;
        nwrite_bytes = m_nwrite_bytes;
        nreads_ext = m_nreads;
        nwrites_ext = m_nwrites;
    }	

protected:
    ComponentModelRegistry& m_registry;
    Clock&                  m_clock;
    std::vector<ClientInfo> m_clients;
    StorageTraceSet         m_storages;
    std::vector<Bank*>      m_banks;
    CycleNo                 m_baseRequestTime;
    CycleNo                 m_timePerLine;
    size_t                  m_lineSize;
    BufferSize              m_bufferSize;
    size_t                  m_cachelineSize;
    IBankSelector*          m_selector;

    uint64_t m_nreads;
    uint64_t m_nread_bytes;
    uint64_t m_nwrites;
    uint64_t m_nwrite_bytes;

public:
    BankedMemory(const std::string& name, Object& parent, Clock& clock, Config& config, const std::string& defaultBankSelectorType);
    ~BankedMemory();
    
    // Debugging
    void Cmd_Info(std::ostream& out, const std::vector<std::string>& arguments) const;
    void Cmd_Read(std::ostream& out, const std::vector<std::string>& arguments) const;
};

}
#endif

