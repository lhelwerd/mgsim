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
#ifdef HAVE_CONFIG_H
#include "sys_config.h"
#endif

#include "simreadline.h"

#include "Processor.h"
#include "FPU.h"
#include "IdealMemory.h"
#include "ParallelMemory.h"
#include "BankedMemory.h"
#include "RandomBankedMemory.h"

#include "commands.h"
#include "config.h"
#include "profile.h"
#include "loader.h"

#include <cassert>
#include <iostream>
#include <iomanip>
#include <stdexcept>
#include <limits>
#include <typeinfo>
#include <cmath>
#include <algorithm>

#include <signal.h>

using namespace Simulator;
using namespace std;

static vector<string> Tokenize(const string& str, const string& sep)
{
    vector<string> tokens;
    for (size_t next, pos = str.find_first_not_of(sep); pos != string::npos; pos = next)
    {
        next = str.find_first_of(sep, pos);
        if (next == string::npos)
        {
            tokens.push_back(str.substr(pos));  
        }
        else
        {
            tokens.push_back(str.substr(pos, next - pos));
            next = str.find_first_not_of(sep, next);
        }
    }
    return tokens;
}

static string Trim(const string& str)
{
    size_t beg = str.find_first_not_of(" \t");
	if (beg != string::npos)
	{
		size_t end = str.find_last_not_of(" \t");
		return str.substr(beg, end - beg + 1);
	}
	return "";
}

class MGSystem : public Object
{
    vector<Processor*> m_procs;
    vector<FPU*>       m_fpus;
    vector<Object*>    m_objects;
    Kernel             m_kernel;
    IMemoryAdmin*      m_memory;

    // Writes the current configuration into memory and returns its address
    MemAddr WriteConfiguration(const Config& config)
    {
        const vector<PSize>& placeSizes = config.getIntegerList<PSize>("NumProcessors");
        
        vector<uint32_t> data(1 + m_procs.size());

        // Store the number of cores
        SerializeRegister(RT_INTEGER, m_procs.size(), &data[0], sizeof data[0]);

        // Store the cores, per place
        PSize first = 0;
        for (size_t p = 0; p < placeSizes.size(); ++p)
        {            
            PSize placeSize = placeSizes[p];
            for (size_t i = 0; i < placeSize; ++i)
            {
                PSize pid = first + i;
                SerializeRegister(RT_INTEGER, (p << 16) | (pid << 0), &data[1 + pid], sizeof data[0]);
            }
            first += placeSize;
        }
        
        MemAddr base;
        if (!m_memory->Allocate(data.size() * sizeof data[0], IMemory::PERM_READ, base))
        {
            throw runtime_error("Unable to allocate memory to store configuration data");
        }
        m_memory->Write(base, &data[0], data.size() * sizeof data[0]);
        return base;
    }

public:
    // Get or set the debug flag
    int  GetDebugMode() const   { return m_kernel.GetDebugMode(); }
    void SetDebugMode(int mode) { m_kernel.SetDebugMode(mode); }

    uint64_t GetOp() const
    {
        uint64_t op = 0;
        for (size_t i = 0; i < m_procs.size(); ++i) {
            op += m_procs[i]->GetOp();
        }
        return op;
    }

    uint64_t GetFlop() const
    {
        uint64_t flop = 0;
        for (size_t i = 0; i < m_procs.size(); ++i) {
            flop += m_procs[i]->GetFlop();
        }
        return flop;
    }

	void PrintState() const
	{
		typedef map<string, RunState> StateMap;
		
		StateMap   states;
		streamsize length = 0;

		const Kernel::CallbackList& callbacks = m_kernel.GetCallbacks();
		for (Kernel::CallbackList::const_iterator p = callbacks.begin(); p != callbacks.end(); ++p)
		{
		    for (size_t i = 0; i < p->second.states.size(); ++i)
		    {
    			string name = p->first->GetFQN() + ":" + p->second.states[i].name + ": ";
    			states[name] = p->second.states[i].state;
    			length = max(length, (streamsize)name.length());
    	    }
		}
		
		cout << left << setfill(' ');
		for (StateMap::const_iterator p = states.begin(); p != states.end(); ++p)
		{
			cout << setw(length) << p->first;
			switch (p->second)
			{
				case STATE_IDLE:     cout << "idle";    break;
				case STATE_DEADLOCK: cout << "stalled"; break;
				case STATE_RUNNING:  cout << "running"; break;
				case STATE_ABORTED:  assert(0); break;
			}
			cout << endl;
		}
		cout << endl;

        int width = (int)log10(m_procs.size()) + 1;
   		for (size_t i = 0; i < m_procs.size(); ++i)
   		{
   		    cout << "Processor " << right << setw(width) << i << ": "
   		         << (m_procs[i]->IsIdle() ? "idle" : "busy") << endl;
   		}
	}

	void PrintRegFileAsyncPortActivity() const
	{
		float avg  = 0;
		float amax = 0.0f;
		float amin = 1.0f;
        for (size_t i = 0; i < m_procs.size(); ++i) {
            float a = m_procs[i]->GetRegFileAsyncPortActivity();
			amax = max(amax, a);
			amin = min(amin, a);
			avg += a;
        }
        avg /= (float)m_procs.size();
		cout << avg << " " << amin << " " << amax;
	}

	void PrintPipelineEfficiency() const
	{
		float avg  = 0;
		float amax = 0.0f;
		float amin = 1.0f;
		size_t num = 0;
        for (size_t i = 0; i < m_procs.size(); ++i) {
            float a = m_procs[i]->GetPipelineEfficiency();
            if (a > 0)
            {
				amax = max(amax, a);
				amin = min(amin, a);
				avg += a;
				num++;
			}
        }
        avg /= (float)num;
		cout << avg << " " << amin << " " << amax;
	}
	
	void PrintActiveQueueSize() const
	{
	    float    avg    = 0;
	    uint64_t amax   = 0;
	    uint64_t amin   = numeric_limits<uint64_t>::max();
	    CycleNo cycles = m_kernel.GetCycleNo();
        for (size_t i = 0; i < m_procs.size(); ++i) {
            float a = (float)m_procs[i]->GetTotalActiveQueueSize() / (float)cycles;
			amax    = max(amax, m_procs[i]->GetMaxActiveQueueSize() );
			amin    = min(amin, m_procs[i]->GetMinActiveQueueSize() );
			avg += a;
        }
        avg /= (float)m_procs.size();
		cout << avg << " " << amin << " " << amax;
	}

	void PrintPipelineIdleTime() const
	{
	    float    avg    = 0;
	    uint64_t amax   = 0;
	    uint64_t amin   = numeric_limits<uint64_t>::max();
        for (size_t i = 0; i < m_procs.size(); ++i) {
            float a = (float)m_procs[i]->GetAvgPipelineIdleTime();
			amax    = max(amax, m_procs[i]->GetMaxPipelineIdleTime() );
			amin    = min(amin, m_procs[i]->GetMinPipelineIdleTime() );
			avg += a;
        }
        avg /= (float)m_procs.size();
        if (avg == 0) {
    		cout << "- - -";
        } else {
    		cout << avg << " " << amin << " " << amax;
    	}
	}

    void PrintFamilyCompletions() const
    {
        CycleNo first = UINT64_MAX;
        CycleNo last  = 0;
        for (size_t i = 0; i < m_procs.size(); ++i) {
            CycleNo cycle = m_procs[i]->GetLocalFamilyCompletion();
            if (cycle != 0)
            {
                first = min(first, cycle);
                last  = max(last,  cycle);
            }
        }
        cout << first << " " << last;
    }

	const Kernel& GetKernel() const { return m_kernel; }
          Kernel& GetKernel()       { return m_kernel; }

    // Find a component in the system given its path
    // Returns NULL when the component is not found
    Object* GetComponent(const string& path)
    {
        Object* cur = this;
        vector<string> names = Tokenize(path, ".");
        for (vector<string>::iterator p = names.begin(); cur != NULL && p != names.end(); ++p)
        {
            transform(p->begin(), p->end(), p->begin(), ::toupper);

            Object* next = NULL;
            for (unsigned int i = 0; i < cur->GetNumChildren(); ++i)
            {
                Object* child = cur->GetChild(i);
                string name   = child->GetName();
                transform(name.begin(), name.end(), name.begin(), ::toupper);
                if (name == *p)
                {
                    next = child;
                    break;
                }
            }
            cur = next;
        }
        return cur;
    }

    // Steps the entire system this many cycles
    RunState Step(CycleNo nCycles)
    {
   		RunState state = GetKernel().Step(nCycles);
   		if (state == STATE_IDLE)
   		{
   		    // An idle state might actually be deadlock if there's a bug in the simulator.
   		    // So check all cores to see if they're really done.
   		    for (size_t i = 0; i < m_procs.size(); ++i)
   		    {
   		        if (!m_procs[i]->IsIdle())
   		        {
   		            return STATE_DEADLOCK;
   		        }
   		    }
   		}
   		return state;
    }
    
    void Abort()
    {
        GetKernel().Abort();
    }
    
    MGSystem(const Config& config, const string& program,
        const vector<pair<RegAddr, RegValue> >& regs,
        const vector<pair<RegAddr, string> >& loads,
        bool quiet)
    : Object(NULL, NULL, "system")
    {
        const vector<PSize> placeSizes = config.getIntegerList<PSize>("NumProcessors");
        const size_t numProcessorsPerFPU_orig = max<size_t>(1, config.getInteger<size_t>("NumProcessorsPerFPU", 1));

        // Validate the #cores/FPU
        size_t numProcessorsPerFPU = numProcessorsPerFPU_orig;
        for (; numProcessorsPerFPU > 1; --numProcessorsPerFPU)
        {
            size_t i;
            for (i = 0; i < placeSizes.size(); ++i) {
                if (placeSizes[i] % numProcessorsPerFPU != 0) {
                    break;
                }
            }
            if (i == placeSizes.size()) break;
        }

        if (numProcessorsPerFPU != numProcessorsPerFPU_orig) {
            fprintf(stderr, "Warning: #cores in at least one place cannot be divided by %u cores/FPU\nValue has been adjusted to %u cores/FPU\n",
                (unsigned)numProcessorsPerFPU_orig,
                (unsigned)numProcessorsPerFPU);
        }
                        
        PSize numProcessors = 0;
        size_t numFPUs      = 0;
        for (size_t i = 0; i < placeSizes.size(); ++i) {
            if (placeSizes[i] % numProcessorsPerFPU != 0) {
                throw runtime_error("#cores in at least one place cannot be divided by #cores/FPU");
            }
            numProcessors += placeSizes[i];
            numFPUs       += placeSizes[i] / numProcessorsPerFPU;
        }
        
        string memory_type = config.getString("MemoryType", "");
        std::transform(memory_type.begin(), memory_type.end(), memory_type.begin(), ::toupper);
        
        m_objects.resize(numProcessors + numFPUs + 1);
        if (memory_type == "IDEAL") {
            IdealMemory* memory = new IdealMemory(this, m_kernel, "memory", config);
            m_objects.back() = memory;
            m_memory = memory;
        } else if (memory_type == "PARALLEL") {
            ParallelMemory* memory = new ParallelMemory(this, m_kernel, "memory", config);
            m_objects.back() = memory;
            m_memory = memory;
        } else if (memory_type == "BANKED") {
            BankedMemory* memory = new BankedMemory(this, m_kernel, "memory", config);
            m_objects.back() = memory;
            m_memory = memory;
        } else if (memory_type == "RANDOMBANKED") {
            RandomBankedMemory* memory = new RandomBankedMemory(this, m_kernel, "memory", config);            
            m_objects.back() = memory;
            m_memory = memory;
        } else {
            throw std::runtime_error("Unknown memory type specified in configuration");
        }
        
        // Load the program into memory
        MemAddr entry = LoadProgram(m_memory, program, quiet);
        
        // Create the FPUs
        m_fpus.resize(numFPUs);
        for (size_t f = 0; f < numFPUs; ++f)
        {
            stringstream name;
            name << "fpu" << f;
            m_fpus[f] = new FPU(this, m_kernel, name.str(), config, numProcessorsPerFPU);
        }

        // Create processor grid
        m_procs.resize(numProcessors);

        PSize first = 0;
        for (size_t p = 0; p < placeSizes.size(); ++p)
        {            
            PSize placeSize = placeSizes[p];
            for (size_t i = 0; i < placeSize; ++i)
            {
                PSize pid = (first + i);
                FPU&  fpu = *m_fpus[pid / numProcessorsPerFPU]; 

                stringstream name;
                name << "cpu" << pid;
                m_procs[pid]   = new Processor(this, m_kernel, pid, i, m_procs, m_procs.size(), placeSize, name.str(), *m_memory, fpu, config, entry);
                m_objects[pid] = m_procs[pid];
            }
            first += placeSize;
        }

        // Connect processors in rings
        first = 0;
        for (size_t p = 0; p < placeSizes.size(); ++p)
        {
            PSize placeSize = placeSizes[p];
            for (size_t i = 0; i < placeSize; ++i)
            {
                PSize pid = (first + i);
                LPID prev = (i + placeSize - 1) % placeSize;
                LPID next = (i + 1) % placeSize;
                m_procs[pid]->Initialize(*m_procs[first + prev], *m_procs[first + next]);
            }
            first += placeSize;
        }
       
        if (!m_procs.empty())
        {
	        // Fill initial registers
	        for (size_t i = 0; i < regs.size(); ++i)
	        {
	        	m_procs[0]->WriteRegister(regs[i].first, regs[i].second);
	        }

            // Load data files	        
            for (size_t i = 0; i < loads.size(); ++i)
            { 
                RegValue value; 
                value.m_state   = RST_FULL; 
                value.m_integer = LoadDataFile(m_memory, loads[i].second, quiet);
                m_procs[0]->WriteRegister(loads[i].first, value); 
            }
            
            // Load configuration
            // Store the address in local #2
			RegValue value;
			value.m_state   = RST_FULL;
            value.m_integer = WriteConfiguration(config);
			m_procs[0]->WriteRegister(MAKE_REGADDR(RT_INTEGER, 2), value);

#if TARGET_ARCH == ARCH_ALPHA
            // The Alpha expects the function address in $27
			value.m_integer = entry;
			m_procs[0]->WriteRegister(MAKE_REGADDR(RT_INTEGER, 27), value);
#endif
        }
    }

    ~MGSystem()
    {
        delete m_memory;
        for (size_t i = 0; i < m_procs.size(); ++i)
        {
            delete m_procs[i];
        }
    }
};

//
// Gets a command line from an input stream
//
static char* GetCommandLine(const string& prompt)
{
    char* str = readline(prompt.c_str());
    if (str != NULL && *str != '\0')
    {
        add_history(str);
    }
    return str;
}

// Return the classname. That's everything after the last ::, if any
// TODO: This doesn't work as well on *NIX. Fix it.
static const char* GetClassName(const type_info& info)
{
    const char* name = info.name();
    const char* pos  = strrchr(name, ':');
    return (pos != NULL) ? pos + 1 : name;
}

// Print all components that are a child of root
static void PrintComponents(const Object* root, const string& indent = "")
{
    for (unsigned int i = 0; i < root->GetNumChildren(); ++i)
    {
        const Object* child = root->GetChild(i);
        string str = indent + child->GetName();

        cout << str << " ";
        for (size_t len = str.length(); len < 30; ++len) cout << " ";
        cout << GetClassName(typeid(*child)) << endl;

        PrintComponents(child, indent + "  ");
    }
}

// Prints the help text
static void PrintHelp()
{
    cout <<
        "Available commands:\n"
        "-------------------\n"
        "(h)elp         Print this help text.\n"
        "(p)rint        Print all components in the system.\n"
        "(s)tep         Advance the system one clock cycle.\n"
        "(r)un          Run the system until it is idle or deadlocks.\n"
        "               Deadlocks or livelocks will not be reported.\n"
        "state          Shows the state of the system.\n"
        "debug [mode]   Show debug mode or set debug mode\n"
        "               Debug mode can be: SIM, PROG or DEADLOCK.\n"
        "               ALL is short for SIM and PROG\n"
        "profiles       Lists the total time of the profiled section.\n"
        "idle           Prints the idle state for all components.\n"
        "\n"
        "help <component>            Show the supported methods and options for this\n"
        "                            component.\n"
        "read <component> <options>  Read data from this component.\n"
        "info <component> <options>  Get general information from this component.\n"
        << endl;
}

static void PrintProfiles()
{
    if (!ProfilingEnabled())
    {
        cout << "Profiling is not enabled." << endl
             << "Please build the simulator with the PROFILE macro defined." << endl;
        return;
    }

    const ProfileMap& profiles = GetProfiles();
    if (profiles.empty())
    {
        cout << "There are no profiles to show" << endl;
    }
    else
    {
        // Get maximum name length and total time
        size_t   length = 0;
        uint64_t total  = 0;
        for (ProfileMap::const_iterator p = profiles.begin(); p != profiles.end(); ++p)
        {
            length = max(length, p->first.length());
            total += p->second;
        }

        for (ProfileMap::const_iterator p = profiles.begin(); p != profiles.end(); ++p)
        {
            cout << setw((streamsize)length) << left << p->first << " "
                 << setw(6) << right << fixed << setprecision(2) << ((float)p->second / 1000000.0f) << "s "
                 << setw(5) << right << fixed << setprecision(1) << ((float)p->second * 100.0f / (float)total) << "%" << endl;
        }
        cout << string(length + 15, '-') << endl;
        cout << setw((streamsize)length) << left << "Total:" << " "
             << setw(6) << right << fixed << setprecision(2) << (float)total / 1000000.0f << "s 100.0%" << endl << endl;
    }
}

static void ExecuteCommand(MGSystem& sys, const string& command, vector<string> args)
{
    // See if the command exists
    int i;
    for (i = 0; Commands[i].name != NULL; ++i)
    {
        if (Commands[i].name == command)
        {
            if (args.size() == 0)
            {
                cout << "Please specify a component. Use \"print\" for a list of all components" << endl;
                break;
            }

            // Pop component name
            Object* obj = sys.GetComponent(args.front());
            args.erase(args.begin());

            if (obj == NULL)
            {
                cout << "Invalid component name" << endl;
            }
            else
            {
                // See if the object type matches
                int j;
                for (j = i; Commands[j].name != NULL && Commands[j].name == command; ++j)
                {
                    if (Commands[j].execute(obj, args))
                    {
                        cout << endl;
                        break;
                    }
                }

                if (Commands[j].name == NULL || Commands[j].name != command)
                {
                    cout << "Invalid argument type for command" << endl;
                }
            }
            break;
        }
    }

    if (Commands[i].name == NULL)
    {
        // Command does not exist
        cout << "Unknown command" << endl;
    }
}

static void PrintUsage()
{
    cout <<
        "MGSim [options] <program-file>\n\n"
        "Options:\n"
        "-h, --help               Show this help\n"
        "-c, --config <filename>  Read configuration from file\n"
        "-q, --quiet              Do not print simulation statistics after run\n" 
        "-i, --interactive        Start the simulator in interactive mode\n"
        "-t, --terminate          Terminate simulator on exception\n"
        "-p, --print <value>      Print the value before printing the results when\n"
        "                         done simulating\n"
        "-R<X> <value>            Store the integer value in the specified register\n"
        "-F<X> <value>            Store the FP value in the specified register\n"
        "-L<X> <filename>         Load the contents of the file after the program\n" 
        "                         and store the address in the specified register\n" 
        "-o, --override <n>=<v>   Overrides the configuration option n with value v\n"
        "\n";
}

struct ProgramConfig
{
    string             m_programFile;
    string             m_configFile;
    bool               m_interactive;
	bool               m_terminate;
	bool               m_quiet;
	string             m_print;
	map<string,string> m_overrides;
	
	vector<pair<RegAddr, RegValue> > m_regs;
    vector<pair<RegAddr, string> >   m_loads;
};

static bool ParseArguments(int argc, const char* argv[], ProgramConfig& config)
{
    config.m_interactive = false;
    config.m_terminate   = false;
    config.m_quiet       = false;
    config.m_configFile  = MGSIM_CONFIG_PATH; 

    for (int i = 1; i < argc; ++i)
    {
        const string arg = argv[i];
        if (arg[0] != '-')
        {
            config.m_programFile = arg;
            if (i != argc - 1)
            {
                cerr << "Warning: ignoring options after program file" << endl;
            }
            break;
        }
        
             if (arg == "-c" || arg == "--config")      config.m_configFile  = argv[++i];
        else if (arg == "-i" || arg == "--interactive") config.m_interactive = true;
        else if (arg == "-t" || arg == "--terminate")   config.m_terminate   = true;
        else if (arg == "-q" || arg == "--quiet")       config.m_quiet       = true;
        else if (arg == "-h" || arg == "--help")        { PrintUsage(); return false; }
        else if (arg == "-p" || arg == "--print")       config.m_print = string(argv[++i]) + " ";
        else if (arg == "-o" || arg == "--override")
        {
            if (argv[++i] == NULL) {
                throw runtime_error("Error: expected configuration option");
            }
            string arg = argv[i];
            string::size_type eq = arg.find_first_of("=");
            if (eq == string::npos) {
                throw runtime_error("Error: malformed configuration override syntax");
            }
            string name = arg.substr(0,eq);
            transform(name.begin(), name.end(), name.begin(), ::toupper);
            config.m_overrides[name] = arg.substr(eq + 1);
        }
        else if (toupper(arg[1]) == 'L')  
        { 
            string filename(argv[++i]); 
            char* endptr; 
            RegAddr  addr; 
            unsigned long index = strtoul(&arg[2], &endptr, 0); 
            if (*endptr != '\0') { 
                throw runtime_error("Error: invalid register specifier in option"); 
            } 
            addr = MAKE_REGADDR(RT_INTEGER, index);                      
            config.m_loads.push_back(make_pair(addr, filename)); 
        } 
        else if (toupper(arg[1]) == 'R' || toupper(arg[1]) == 'F')
        {
         	stringstream value;
            value << argv[++i];

            RegAddr  addr;
            RegValue val;

            char* endptr;
            unsigned long index = strtoul(&arg[2], &endptr, 0);
            if (*endptr != '\0') {
             	throw runtime_error("Error: invalid register specifier in option");
            }
                
         	if (toupper(arg[1]) == 'R') {
          		value >> *(signed Integer*)&val.m_integer;
           		addr = MAKE_REGADDR(RT_INTEGER, index);
           	} else {
           		double f;
           		value >> f;
           		val.m_float.fromfloat(f);
           		addr = MAKE_REGADDR(RT_FLOAT, index);
           	}
      		if (value.fail()) {
       			throw runtime_error("Error: invalid value for register");
           	}
           	val.m_state = RST_FULL;
            config.m_regs.push_back(make_pair(addr, val));
        }
    }

    if (config.m_programFile.empty())
    {
        throw runtime_error("Error: no program file specified");
    }

    return true;
}

/// The currently active system, for the signal handler
static MGSystem* active_system = NULL;

static void sigabrt_handler(int)
{
    if (active_system != NULL)
    {
        active_system->Abort();
        active_system = NULL;
    }
}

static RunState StepSystem(MGSystem& system, CycleNo cycles)
{
    active_system = &system;

    struct sigaction new_handler, old_handler;
    new_handler.sa_handler = sigabrt_handler;
    new_handler.sa_flags   = 0;
    sigemptyset(&new_handler.sa_mask);
    sigaction(SIGINT, &new_handler, &old_handler);

    RunState state;
    try
    {
        state = system.Step(cycles);
    }
    catch (...)
    {
        sigaction(SIGINT, &old_handler, NULL);
        throw;
    }
    sigaction(SIGINT, &old_handler, NULL);
    return state;
}
    
int main(int argc, const char* argv[])
{
    try
    {
        // Parse command line arguments
        ProgramConfig config;
        if (!ParseArguments(argc, argv, config))
        {
            return 0;
        }

        // Read configuration
        Config configfile(config.m_configFile, config.m_overrides);

        if (config.m_interactive)
        {
            // Interactive mode
            cout << "Microthreaded Alpha System Simulator, version 1.0" << endl;
            cout << "Created by Mike Lankamp at the University of Amsterdam" << endl << endl;
		}

        // Create the system
		MGSystem sys(configfile, config.m_programFile, config.m_regs, config.m_loads, !config.m_interactive);

        bool interactive = config.m_interactive;
        if (!interactive)
        {
            // Non-interactive mode; run and dump cycle count
            try
            {
                RunState state = StepSystem(sys, INFINITE_CYCLES);
                if (state == STATE_DEADLOCK)
    			{
    				throw runtime_error("Deadlock!");
    			}
    			
    			if (state == STATE_ABORTED)
    			{
    			    throw runtime_error("Aborted!");
    			}
    			
    			if (!config.m_quiet)
    			{
                    cout.rdbuf(cerr.rdbuf());
    			    cout << dec
    			         << config.m_print << sys.GetKernel().GetCycleNo() << " ; "
                         << sys.GetOp() << " "
                         << sys.GetFlop() << " ; ";
    			    sys.PrintRegFileAsyncPortActivity();
    			    cout << " ; ";
    			    sys.PrintActiveQueueSize();
    			    cout << " ; ";
    			    sys.PrintPipelineIdleTime();
    			    cout << " ; ";
    			    sys.PrintPipelineEfficiency();
                    cout << " ; ";
                    sys.PrintFamilyCompletions();
    			    cout << endl;
    			}
    		}
    		catch (exception& e)
    		{
                if (config.m_terminate) 
                {
                    // We do not want to go to interactive mode,
                    // rethrow so it abort the program.
                    throw;
                }
    		    cerr << endl << e.what() << endl;
    		    
    		    // When we get an exception in non-interactive mode,
    		    // jump into interactive mode
        		interactive = true;
    		}
        }
        
        if (interactive)
        {
            // Command loop
            vector<string> prevCommands;
			cout << endl;
            for (bool quit = false; !quit; )
            {
                stringstream prompt;
                prompt << dec << setw(8) << setfill('0') << right << sys.GetKernel().GetCycleNo() << "> ";
            
				// Read the command line and split into commands
				char* line = GetCommandLine(prompt.str());
				if (line == NULL)
				{
				    // End of input
				    cout << endl;
				    break;
				}
				
				vector<string> commands = Tokenize(line, ";");
				if (commands.size() == 0)
				{
					// Empty line, use previous command line
					commands = prevCommands;
				}
				prevCommands = commands;
				free(line);

				// Execute all commands
				for (vector<string>::const_iterator command = commands.begin(); command != commands.end() && !quit; ++command)
				{
					vector<string> args = Tokenize(Trim(*command), " ");
					if (args.size() > 0)
					{
						// Pop the command from the front
						string command = args[0];
						args.erase(args.begin());

						if (command == "h" || command == "/?" || (command == "help" && args.empty()))
						{
							PrintHelp();
						}
						else if (command == "r" || command == "run" || command == "s" || command == "step")
						{
							// Step of run
							CycleNo nCycles = INFINITE_CYCLES;
							if (command[0] == 's')
							{
								// Step
								char* endptr;
								nCycles = args.empty() ? 1 : max(1UL, strtoul(args[0].c_str(), &endptr, 0));
							}

                            try
                            {
                                RunState state = StepSystem(sys, nCycles);
                                if (state == STATE_DEADLOCK)
    							{
    								throw runtime_error("Deadlock!");
    							}
    							
    							if (state == STATE_ABORTED)
    							{
    							    throw runtime_error("Aborted!");
    							}
    					    }
    					    catch (exception& e)
    					    {
    					        cout << e.what() << endl;
    					    }
						}
						else if (command == "p" || command == "print")
						{
							PrintComponents(&sys);
						}
						else if (command == "exit" || command == "quit")
						{
							cout << "Thank you. Come again!" << endl;
							quit = true;
							break;
						}
						else if (command == "profiles")
						{
							PrintProfiles();
						}
						else if (command == "state")
						{
							sys.PrintState();
						}
						else if (command == "debug")
						{
							string state;
							if (!args.empty())
							{
								state = args[0];
								transform(state.begin(), state.end(), state.begin(), ::toupper);
							}
	        
                                 if (state == "SIM")      sys.SetDebugMode(Kernel::DEBUG_SIM);
                            else if (state == "PROG")     sys.SetDebugMode(Kernel::DEBUG_PROG);
                            else if (state == "DEADLOCK") sys.SetDebugMode(Kernel::DEBUG_DEADLOCK);
                            else if (state == "ALL")      sys.SetDebugMode(Kernel::DEBUG_PROG | Kernel::DEBUG_SIM);
                            
                            string debugStr;
                            switch (sys.GetDebugMode())
                            {
                            default:                                     debugStr = "nothing";   break;
                            case Kernel::DEBUG_PROG:                     debugStr = "program";   break;
                            case Kernel::DEBUG_SIM:                      debugStr = "simulator"; break;
                            case Kernel::DEBUG_DEADLOCK:                 debugStr = "deadlocks"; break;
                            case Kernel::DEBUG_PROG | Kernel::DEBUG_SIM: debugStr = "simulator and program"; break;
                            }
						    cout << "Debugging " << debugStr << endl;
						}
						else
						{
							ExecuteCommand(sys, command, args);
						}
					}
				}
			}
	    }
	}
    catch (exception &e)
    {
        cerr << e.what() << endl;
        return 1;
    }
    return 0;
}
