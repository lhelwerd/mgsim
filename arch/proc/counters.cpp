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
#include "Processor.h"
#include <sys/time.h>
#include <ctime>

namespace Simulator
{

size_t Processor::PerfCounters::GetSize() const { return  18 * sizeof(Integer);  }

Result Processor::PerfCounters::Read(MemAddr address, void *data, MemSize size, LFID fid, TID tid, const RegAddr& writeback)
{
    if (size != sizeof(Integer))
        return FAILED;

    address /= sizeof(Integer);

    Processor& cpu = GetMatchUnit().GetProcessor();

    const size_t placeSize  = cpu.m_familyTable[fid].placeSize;
    const size_t placeStart = (cpu.m_pid / placeSize) * placeSize;
    const size_t placeEnd   = placeStart + placeSize;
    Integer value;

    switch (address)
    {
    case 0:
    {
        // Return the number of elapsed cycles
        value = (Integer)GetKernel()->GetCycleNo();
    }
    break;
    case 1:
    {
        // Return the number of executed instructions on all cores
        Integer ops = 0;
        for (size_t i = placeStart; i < placeEnd; ++i)
        {
            ops += cpu.m_grid[i]->GetPipeline().GetOp();
        }
        value = ops;
    }
    break;    
    case 2:
    {
        // Return the number of issued FP instructions on all cores
        Integer flops = 0;
        for (size_t i = placeStart; i < placeEnd; ++i)
        {
            flops += cpu.m_grid[i]->GetPipeline().GetFlop();
        }
        value = flops;
    }
    break;
    case 3:
    {
        // Return the number of completed loads on all cores
        uint64_t n = 0, dummy;
        for (size_t i = placeStart; i < placeEnd; ++i)
        {
            cpu.m_grid[i]->GetPipeline().CollectMemOpStatistics(n, dummy, dummy, dummy);
        }
        value = (Integer)n;
    }
    break;
    case 4:
    {
        // Return the number of completed stores on all cores
        uint64_t n = 0, dummy;
        for (size_t i = placeStart; i < placeEnd; ++i)
        {
            cpu.m_grid[i]->GetPipeline().CollectMemOpStatistics(dummy, n, dummy, dummy);
        }
        value = (Integer)n;
    }
    break;
    case 5:
    {
        // Return the number of successfully loaded bytes on all cores
        uint64_t n = 0, dummy;
        for (size_t i = placeStart; i < placeEnd; ++i)
        {
            cpu.m_grid[i]->GetPipeline().CollectMemOpStatistics(dummy, dummy, n, dummy);
        }
        value = (Integer)n;
    }
    break;
    case 6:
    {
        // Return the number of successfully stored bytes on all cores
        uint64_t n = 0, dummy;
        for (size_t i = placeStart; i < placeEnd; ++i)
        {
            cpu.m_grid[i]->GetPipeline().CollectMemOpStatistics(dummy, dummy, dummy, n);
        }
        value = (Integer)n;
    }
    break;
    case 7:
    {
        // Return the number of memory loads overall from L1 to L2 (cache lines)
        uint64_t n = 0, dummy;
        cpu.m_memory.GetMemoryStatistics(n, dummy, dummy, dummy, dummy, dummy);
        value = (Integer)n;
    }
    break;
    case 8:
    {
        // Return the number of memory stores overall from L1 to L2 (cache lines)
        uint64_t n = 0, dummy;
        cpu.m_memory.GetMemoryStatistics(dummy, n, dummy, dummy, dummy, dummy);
        value = (Integer)n;
    }
    break;
    case 9:
    {
        value = (Integer)placeSize;
    }
    break;
    case 10:
    {
        // Return the total cumulative allocated thread slots
        Integer alloc = 0;
        for (size_t i = placeStart; i < placeEnd; ++i)
        {
            alloc += cpu.m_grid[i]->GetTotalThreadsAllocated();
        }
        value = alloc;
    }
    break;
    case 11:
    {
        // Return the total cumulative allocated thread slots
        Integer alloc = 0;
        for (size_t i = placeStart; i < placeEnd; ++i)
        {
            alloc += cpu.m_grid[i]->GetTotalFamiliesAllocated();
        }
        value = alloc;
    }
    break;
    case 12:
    {
        // Return the total cumulative exclusive allocate queue size
        Integer alloc = 0;
        for (size_t i = placeStart; i < placeEnd; ++i)
        {
            alloc += cpu.m_grid[i]->GetTotalAllocateExQueueSize();
        }
        value = alloc;
    }
    break;
    case 13:
    {
        // Return the Unix time
        value = (Integer)time(0);
    }
    break;
    case 14:
    {
        // Return the local date as a packed struct
        // bits 0-4: day in month
        // bits 5-8: month in year
        // bits 9-31: year from 1900
        time_t c = time(0);
        struct tm * tm = gmtime(&c);
        value = (Integer)tm->tm_mday |
            ((Integer)tm->tm_mon << 5) |
            ((Integer)tm->tm_year << 9);
    }
    break;
    case 15:
    {
        // Return the local time as a packed struct
        // bits 0-14 = microseconds / 2^17  (topmost 15 bits)
        // bits 15-20 = seconds
        // bits 21-26 = minutes
        // bits 27-31 = hours
        struct timeval tv;
        gettimeofday(&tv, 0);
        struct tm * tm = gmtime(&tv.tv_sec);

        // get topmost 15 bits of precision of the usec field
        Integer usec = (tv.tv_usec >> (32-15)) & 0x7fff;
        value = usec | (tm->tm_sec << 15) | (tm->tm_min << 21) | (tm->tm_hour << 27);
    }       
    break;        
    case 16:
    {
        // Return the number of memory loads overall from external memory (cache lines)
        uint64_t n = 0, dummy;
        cpu.m_memory.GetMemoryStatistics(dummy, dummy, dummy, dummy, n, dummy);
        value = (Integer)n;
    }
    break;
    case 17:
    {
        // Return the number of memory stores overall to external memory (cache lines)
        uint64_t n = 0, dummy;
        cpu.m_memory.GetMemoryStatistics(dummy, dummy, dummy, dummy, dummy, n);
        value = (Integer)n;
    }
    break;
    default:
        value = 0;
    }

    DebugIOWrite("Read counter %u by F%u/T%u: %#016llx (%llu)",
                 (unsigned)address, (unsigned)fid, (unsigned)tid, 
                 (unsigned long long)value, (unsigned long long)value);


    if (address == 0)
    {
        ++m_nCycleSampleOps;
    }
    else
    {
        ++m_nOtherSampleOps;
    }

    SerializeRegister(RT_INTEGER, value, data, sizeof(Integer));

    return SUCCESS;
}

Processor::PerfCounters::PerfCounters(IOMatchUnit& parent)
    : Processor::MMIOComponent("perfcounters", parent, parent.GetProcessor().GetClock()),
      m_nCycleSampleOps(0),
      m_nOtherSampleOps(0)
{
    RegisterSampleVariableInObject(m_nCycleSampleOps, SVC_CUMULATIVE);
    RegisterSampleVariableInObject(m_nOtherSampleOps, SVC_CUMULATIVE);
}

}
