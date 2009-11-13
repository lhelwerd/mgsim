/*
mgsim: Microgrid Simulator
Copyright (C) 2006,2007,2008,2009  The Microgrid Project.

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
#include "memorydatacontainer.h"
#include "stdlib.h"
#include "assert.h"

MemoryDataContainer* MemoryDataContainer::s_pDataContainer = NULL;

MemoryDataContainer::MemoryDataContainer()
{
    // currently only one data container is allowed in the simulation system. 
    if (s_pDataContainer == NULL)
        s_pDataContainer = this;
    else
    {
        assert(false);
    }
}
