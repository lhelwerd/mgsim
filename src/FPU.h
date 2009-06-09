#ifndef FPU_H
#define FPU_H

#include "buffer.h"
#include "ports.h"
#include <deque>
#include <map>

class Config;

namespace Simulator
{

class Processor;
class RegisterFile;

/**
 * The different kinds of floating point operations that the FPU can perform
 */
enum FPUOperation
{
    FPU_OP_NONE = -1,   ///< Reserved for internal use
    FPU_OP_ADD  =  0,   ///< Addition
    FPU_OP_SUB,         ///< Subtraction
    FPU_OP_MUL,         ///< Multiplication
    FPU_OP_DIV,         ///< Division
    FPU_OP_SQRT,        ///< Square root
    FPU_NUM_OPS         ///< Number of operations
};

/**
 * @brief Floating Point Unit
 *
 * This component accepts floating point operations, executes them asynchronously and writes them
 * back once calculated. It has several pipelines, assuming every operation of equal delay can be pipelined.
 */
class FPU : public IComponent
{
    /// Represents an FP operation
    struct Operation
    {
	    FPUOperation op;
	    int          size;
	    double       Rav, Rbv;
	    RegAddr      Rc;
    };

    /// Represents a source for this FPU    
	struct Source
	{
	    Buffer<Operation> inputs;   ///< Input queue for operations from this source
	    RegisterFile*     regfile;  ///< Register file to write back results for this source
	    
	    Source(Kernel& kernel, BufferSize bufferSize)
	        : inputs(kernel, bufferSize), regfile(NULL) {}
	};
	
    /// Represents the result of an FP operation
	struct Result
	{
		RegAddr       address;     ///< Address of destination register of result.
		Source*       source;      ///< The source of the operation
		MultiFloat    value;       ///< Resulting value of the operation.
		int           size;        ///< Size of the resulting value.
		unsigned int  state;       ///< Progression through the pipeline.
	};

    /// Represents a pipeline for an FP operation type
	struct Unit
	{
	    ArbitratedService  service;     ///< Arbitrator
	    bool               pipelined;   ///< Is it a pipeline or a single ex. unit?
	    CycleNo            latency;     ///< The latency of the unit/pipeline
	    std::deque<Result> slots;       ///< The pipeline slots
	    
	    Unit(const Object& object, const std::string& name);
	};
	
    /**
     * Called when an operation has completed.
     * @param res the result to write back to the register file.
     * @return true if the result could be written back to the register file.
     */
	bool OnCompletion(const Result& res) const;
	
	/**
	 * Called in order to compute the result from a queued operation
	 * @param op    [in] the operation with source information
	 * @param start [in] the cycle number when the FP operation started
	 * @return the result of the source operation
	 */
    Result CalculateResult(const Operation& op) const;
	
	Simulator::Result OnCycleWritePhase(unsigned int stateIndex);

	std::vector<Source> m_sources;               ///< Data for the sources for this FPU
	std::vector<Unit*>  m_units;                 ///< The execution units in the FPU
	std::vector<size_t> m_mapping[FPU_NUM_OPS];  ///< List of units for each FPU op

    void Cleanup();
public:
    /// Returns the number of execution units (states that can write back)
    size_t GetNumExecutionUnits() const { return m_units.size(); }

    /**
     * @brief Constructs the FPU.
     * @param parent     reference to the parent object
     * @param kernel     the kernel to manage this FPU
     * @param name       name of the FPU, irrelevant to simulation
     * @param config     reference to the configuration data
     * @param num_inputs number of inputs that will be connected to this FPU
     */
    FPU(Object* parent, Kernel& kernel, const std::string& name, const Config& config, size_t num_inputs);
    
    /// Destroys the FPU object
    ~FPU();

	/**
	 * @brief Registers a source to the FPU
	 * @param regfile [in] the register file to use to write back results for this source
	 * @return the unique for this source to be passed to QueueOperation
	 */
	size_t RegisterSource(RegisterFile& regfile);
	
    /**
     * @brief Queues an FP operation.
     * @details This function determines the length of the operation and queues the operation in the corresponding
     *      pipeline. When the operation has completed, the result is written back to the register file.
     * @param source  the source input ID
     * @param op      the FP operation to perform
     * @param size    size of the FP operation (4 or 8)
     * @param Rav     first (or only) operand of the operation
     * @param Rbv     second operand of the operation
     * @param Rc      address of the destination register(s)
     * @return true if the operation could be queued.
     */
	bool QueueOperation(size_t source, FPUOperation op, int size, double Rav, double Rbv, const RegAddr& Rc);
};

}
#endif

