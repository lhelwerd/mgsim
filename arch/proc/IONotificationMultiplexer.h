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
#ifndef IONMUX_H
#define IONMUX_H

#ifndef PROCESSOR_H
#error This file should be included in Processor.h
#endif

class IOBusInterface;

class IONotificationMultiplexer : public Object
{
private:
    RegisterFile&                   m_regFile;
    Allocator&                   m_allocator;

    std::vector<Register<RegAddr>*> m_writebacks;

    StorageTraceSet GetInterruptRequestTraces() const;
    StorageTraceSet GetNotificationTraces() const;

public:
    std::vector<bool>               m_mask;
    std::vector<SingleFlag*>        m_interrupts;
    std::vector<Buffer<Integer>*>   m_notifications;

private:
    size_t                          m_lastNotified;

public:
    IONotificationMultiplexer(const std::string& name, Object& parent, Clock& clock, RegisterFile& rf, Allocator& alloc, size_t numChannels, Config& config);
    ~IONotificationMultiplexer();

    // sent by device select upon an I/O read from the processor
    bool SetWriteBackAddress(IONotificationChannelID which, const RegAddr& addr);
    bool ConfigureChannel(IONotificationChannelID which, Integer mode);

    // triggered by the IOBusInterface
    bool OnInterruptRequestReceived(IONotificationChannelID which);
    bool OnNotificationReceived(IONotificationChannelID which, Integer tag);

    Process p_IncomingNotifications;
    
    // upon interrupt received
    Result DoReceivedNotifications();
};


#endif
