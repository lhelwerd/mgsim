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
#ifndef IOINTERFACE_H
#define IOINTERFACE_H

#ifndef PROCESSOR_H
#error This file should be included in Processor.h
#endif

#include "IOResponseMultiplexer.h"
#include "IOInterruptMultiplexer.h"
#include "IOBusInterface.h"

class IOInterface : public Object, public Inspect::Interface<Inspect::Info>
{
public:
    class AsyncIOInterface : public MMIOComponent, public Inspect::Interface<Inspect::Info>
    {
    private:
        unsigned                m_devAddrBits;
        size_t                  m_numDeviceSlots;

        IOInterface&  GetInterface();
    public:
        AsyncIOInterface(const std::string& name, IOInterface& parent, Clock& clock, size_t numDevices, const Config& config);

        size_t GetSize() const;

        Result Read (MemAddr address, void* data, MemSize size, LFID fid, TID tid, const RegAddr& writeback);
        Result Write(MemAddr address, const void* data, MemSize size, LFID fid, TID tid);

        void Cmd_Info(std::ostream& out, const std::vector<std::string>& args) const;
        void Cmd_Help(std::ostream& out, const std::vector<std::string>& args) const;
    };

    class PICInterface : public MMIOComponent, public Inspect::Interface<Inspect::Info>
    {
    private:
        size_t                  m_numInterrupts;

        IOInterface&  GetInterface();
    public:
        PICInterface(const std::string& name, IOInterface& parent, Clock& clock, size_t numInterrupts, const Config& config);

        size_t GetSize() const;

        Result Read (MemAddr address, void* data, MemSize size, LFID fid, TID tid, const RegAddr& writeback);
        Result Write(MemAddr address, const void* data, MemSize size, LFID fid, TID tid);

        void Cmd_Info(std::ostream& out, const std::vector<std::string>& args) const;
        void Cmd_Help(std::ostream& out, const std::vector<std::string>& args) const;
    };
    

private:
    size_t                      m_numDevices;
    size_t                      m_numInterrupts;

    friend class AsyncIOInterface;
    AsyncIOInterface m_async_io;

    friend class PICInterface;
    PICInterface m_pic;        

    IOResponseMultiplexer   m_rrmux;
    IOInterruptMultiplexer  m_intmux;
    IOBusInterface          m_iobus_if;

    bool Read(IODeviceID dev, MemAddr address, MemSize size, const RegAddr& writeback);
    bool Write(IODeviceID dev, MemAddr address, const IOData& data);
    bool WaitForNotification(IOInterruptID dev, const RegAddr& writeback);

public:
    IOInterface(const std::string& name, Object& parent, Clock& clock, RegisterFile& rf, IIOBus& iobus, IODeviceID devid, const Config& config);

    MMIOComponent& GetAsyncIOInterface() { return m_async_io; }
    MMIOComponent& GetPICInterface() { return m_pic; }

    IOResponseMultiplexer& GetReadResponseMultiplexer() { return m_rrmux; }
    IOInterruptMultiplexer& GetInterruptMultiplexer() { return m_intmux; }
    
    // Debugging
    void Cmd_Info(std::ostream& out, const std::vector<std::string>& args) const;
    void Cmd_Help(std::ostream& out, const std::vector<std::string>& args) const;
};


#endif
