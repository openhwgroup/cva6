/*
 *
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 *
 * The contents of this file are provided under the Software License
 * Agreement that you accepted before downloading this file.
 *
 * This source forms part of the Software and can be used for educational,
 * training, and demonstration purposes but cannot be used for derivative
 * works except in cases where the derivative works require OVP technology
 * to run.
 *
 * For open source models released under licenses that you can use for
 * derivative works, please visit www.OVPworld.org or www.imperas.com
 * for the location of the open source models.
 *
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "op/op.h"

//
// DPI imported/exported functions
//

/* DPI imports */
int cpu_init(const int , const char *, const char *, const char *, const char *, const int );
int cpu_term(/*const int,  const char * */);

/* DPI exports */
extern int busWait();
extern int setRETIRE();
extern void getState(int *_terminate, int *_reset, int *_nmi, int *_MSWInterrupt, int *_USWInterrupt, int *_SSWInterrupt, int *_MTimerInterrupt, int *_UTimerInterrupt, int *_STimerInterrupt, int *_MExternalInterrupt, int *_UExternalInterrupt, int *_SExternalInterrupt);
extern void setDECODE(const void *value);
extern void setGPR(const int index, const long long value);
extern void setFPR(const int index, const long long value);
extern void setCSR(const void *index, const long long value);
extern void setPC(const long long value);
extern int busWrite(const int address, const int size, const int data, const int artifact);
extern int busRead(const int address, const int size, int *data, const int artifact, const int ifetch);

#define SHELL_NAME "CPU"

#define DEBUG 0

typedef struct svNetS {
    int     value;
    optNetP net;
} svNetT, *svNetP;

typedef struct svStateS {
    optProcessorP processor;
    Uns64 icount, finishafter;
    Uns64 pc;
    Uns64 gpr[32];
    Uns64 fpr[32];
    Uns64 mcsr[4096];
    Uns64 ucsr[4096];
    Uns64 scsr[4096];

    svNetT terminate;

    svNetT reset;
    svNetT nmi;
    svNetT MSWInterrupt;
    svNetT USWInterrupt;
    svNetT SSWInterrupt;
    svNetT MTimerInterrupt;
    svNetT UTimerInterrupt;
    svNetT STimerInterrupt;
    svNetT MExternalInterrupt;
    svNetT UExternalInterrupt;
    svNetT SExternalInterrupt;
} svStateT, *svStateP;

svStateT svState[128];

OP_BUS_SLAVE_READ_FN(busReadCB) {
    const char *access = "LOAD ";
    if (isFetch) access = "FETCH";

    const char *master = initiator.Processor ? opObjectHierName(initiator.Processor) : "artifact";

    Int32 value = 0;
    Int32 tmpV  = 0;
    Uns32 index = 0;
    if(!initiator.Processor) {
        if (DEBUG) {
            opMessage("I", access, "%s access %d bytes at address 0x" FMT_Ax, master, bytes, addr);
        }

        // Artifact access - perform as bytes
        for (index=0;index < bytes;index++) {
            busRead(addr+index, 1, &value, 1, isFetch);
            if (DEBUG) {
                opMessage("I", access, "  %s %d bytes at address 0x" FMT_Ax " data 0x%08x",
                    master, 1, addr+index, value);
            }
            *(Uns8 *)(data+index) = value;
        }
    } else {
        switch (bytes) {
        case 1:
            busRead(addr, 1, &value, 0, isFetch);
            *(Uns8 *)data = value;
            break;
        case 2:
            switch(addr&1) {
                case 1:
                    // not aligned, split access
                    busRead(addr,   1, &tmpV, 0, isFetch);
                    value = tmpV;
                    busRead(addr+1, 1, &tmpV, 0, isFetch);
                    value |= (tmpV << 8);
                    break;
                case 0:
                    // aligned
                    busRead(addr, 2, &value, 0, isFetch);
                    break;
            }
            *(Uns16 *)data = value;
            break;
        case 4:
            switch(addr&3) {
                case 0:
                    // aligned
                    busRead(addr, 4, &value, 0, isFetch);
                    break;
                case 1:
                case 3:
                    // not aligned, split access
                    busRead(addr+0, 1, &tmpV, 0, isFetch);
                    value |= (tmpV      );
                    busRead(addr+1, 2, &tmpV, 0, isFetch);
                    value |= (tmpV <<  8);
                    busRead(addr+3, 1, &value, 0, isFetch);
                    value |= (tmpV << 24);
                    break;
                case 2:
                    // not aligned, split access
                    busRead(addr+0, 2, &tmpV, 0, isFetch);
                    value |= tmpV;
                    busRead(addr+2, 2, &tmpV, 0, isFetch);
                    value |= (tmpV << 16);
            }
            *(Uns32 *)data = value;
            break;
        case 8:
            if(addr&7) {
                opMessage("F", "READ", " bytes %d addr&7 %d (8 bytes unaligned not supported in implementation)", bytes, (Uns32)addr&7);
            } else {
                busRead(addr, 4, &value, 0, isFetch);
                *(Uns32 *)(data) = value;
                // second access
                busRead(addr+4, 4, &value, 0, isFetch);
                *(Uns32 *)(data+4) = value;
            }
            break;
        default:
            opMessage("F", "READ", " bytes %d (1,2,4,8 bytes supported in implementation)", bytes);
            break;
        }

        if (DEBUG) {
            opMessage("I", access, "%s %d bytes at address 0x" FMT_Ax " data 0x%08x",
                master, bytes, addr, value);
        }
    }
}

OP_BUS_SLAVE_WRITE_FN(busWriteCB) {
    const char *access = "STORE";

    const char *master = initiator.Processor ? opObjectHierName(initiator.Processor) : "artifact";

    Uns32 value = 0;
    Uns32 tmpV  = 0;
    Uns32 index = 0;

    if(!initiator.Processor) {
        if (DEBUG) {
            opMessage("I", access, "%s %d bytes at address 0x" FMT_Ax " data 0x%08x",
                master, bytes, addr, *(Uns32 *)data);
        }
        // Artifact access - perform as bytes
        for (index=0;index < bytes;index++) {
            value = *(Uns8 *)(data+index);
            if (DEBUG) {
                opMessage("I", access, "  %s %d bytes at address 0x" FMT_Ax " data 0x%08x",
                    master, 1, addr+index, value);
            }
            busWrite(addr+index, 1, value, 1);
        }
    } else {
        // real access
        switch (bytes) {
        case 1:
            value = *(Uns8 *)data;
            busWrite(addr, 1, value, 0);
            break;
        case 2:
            value = *(Uns16 *)data;
            switch(addr&1) {
                case 1:
                    // not aligned, split access
                    tmpV = value & 0xff;
                    busWrite(addr,   1, tmpV, 0);
                    tmpV = (value >> 8) & 0xff;
                    busWrite(addr+1, 1, tmpV, 0);
                    break;
                case 0:
                    // aligned
                    busWrite(addr, 2, value, 0);
                    break;
            }
            break;
        case 4:
            value = *(Uns32 *)(data);
            switch(addr&3) {
                case 0:
                    // aligned
                    busWrite(addr, 4, value, 0);
                    break;
                case 1:
                case 3:
                    // not aligned, split access
                    tmpV = value & 0xff;
                    busWrite(addr+0, 1, tmpV, 0);
                    tmpV = (value >> 8) & 0xffff;
                    busWrite(addr+1, 2, tmpV, 0);
                    tmpV = (value >> 24) & 0xff;
                    busWrite(addr+3, 1, tmpV, 0);
                    break;
                case 2:
                    // not aligned, split access
                    tmpV = value & 0xffff;
                    busWrite(addr+0, 2, tmpV, 0);
                    tmpV = (value >> 16) & 0xffff;
                    busWrite(addr+2, 2, tmpV, 0);
            }
            break;
        case 8:
            if(addr&7) {
                opMessage("F", "WRITE", " bytes %d addr&7 %d (8 bytes unaligned not supported in implementation)", bytes, (Uns32)addr&7);
            } else {
                value = *(Uns32 *)(data);
                busWrite(addr, 4, value, 0);
                value = *(Uns32 *)(data+4);
                busWrite(addr+4, 4, value, 0);
            }
            break;
        default:
            opMessage("F", "WRITE", " bytes %d (1,2,4,8 bytes supported in implementation)", bytes);
            break;
        }
        if (DEBUG) {
            opMessage("I", "WRITE", " address 0x" FMT_Ax " bytes %d data 0x%08x",
                addr, bytes, value);
        }
    }
}

static char *dupName (const char *name, int id) {
    char tmp[128];
    sprintf(tmp, "%s%d", name, id);
    return strdup(tmp);
}

// instantiate module components
static optProcessorP cpu_create(
        optModuleP mi, Int32 id,
        const char *vendor, const char *variant, Uns32 addressBits,
        const char *program) {

    optBusP bus_b = opBusNew(mi, dupName("bus", id), addressBits, 0, 0);

    svState[id].reset.net              = opNetNew(mi, dupName("reset",              id), 0, 0);
    svState[id].nmi.net                = opNetNew(mi, dupName("nmi",                id), 0, 0);
    svState[id].MSWInterrupt.net       = opNetNew(mi, dupName("MSWInterrupt",       id), 0, 0);
    svState[id].USWInterrupt.net       = opNetNew(mi, dupName("USWInterrupt",       id), 0, 0);
    svState[id].SSWInterrupt.net       = opNetNew(mi, dupName("SSWInterrupt",       id), 0, 0);
    svState[id].MTimerInterrupt.net    = opNetNew(mi, dupName("MTimerInterrupt",    id), 0, 0);
    svState[id].UTimerInterrupt.net    = opNetNew(mi, dupName("UTimerInterrupt",    id), 0, 0);
    svState[id].STimerInterrupt.net    = opNetNew(mi, dupName("STimerInterrupt",    id), 0, 0);
    svState[id].MExternalInterrupt.net = opNetNew(mi, dupName("MExternalInterrupt", id), 0, 0);
    svState[id].UExternalInterrupt.net = opNetNew(mi, dupName("UExternalInterrupt", id), 0, 0);
    svState[id].SExternalInterrupt.net = opNetNew(mi, dupName("SExternalInterrupt", id), 0, 0);


    // Processor cpu
    const char *cpu_path = opVLNVString(
        0,  vendor, 0, "riscv", "1.0", OP_PROCESSOR, 1   // report errors
    );
    // Processor Semihost for exit Control
    const char *semihost_path = opVLNVString(
        0,  vendor, 0, "exitControl", "1.0", OP_EXTENSION, 1   // report errors
    );


    optProcessorP processor = opProcessorNewWithSemihost(
        mi, cpu_path, dupName("cpu", id),
        OP_CONNECTIONS(
            OP_BUS_CONNECTIONS(
                OP_BUS_CONNECT(bus_b, "INSTRUCTION"),
                OP_BUS_CONNECT(bus_b, "DATA")
            ),
            OP_NET_CONNECTIONS(
                OP_NET_CONNECT(svState[id].reset.net,              "reset"),
                OP_NET_CONNECT(svState[id].MExternalInterrupt.net, "MExternalInterrupt")
            )
        ),
        OP_PARAMS(
                OP_PARAM_STRING_SET("variant", variant),
                OP_PARAM_BOOL_SET(OP_FP_SIMULATEEXCEPTIONS, 1)),
        semihost_path
    );

    if(!processor) {
        opMessage("E", SHELL_NAME, "Processor instance (%s / processor / riscv / 1.0) creation failed.", vendor);
    }

    // Memory Read/Write Callbacks

    Uns64 addrLow  = 0;
    Uns64 addrHigh = -1ULL;
    if(addressBits!=64) {
        addrHigh = (1ULL<<addressBits)-1;
    }

    opBusSlaveNew(
        bus_b, "Memory", processor, OP_PRIV_RWX,
        addrLow, addrHigh,
        busReadCB, busWriteCB,
        0, 0);

    if(!opProcessorApplicationLoad (processor, program, OP_LDR_SET_START, 0x0)) {
        opMessage("E", SHELL_NAME, "Application load on processor %s with program %s failed",
                                        opObjectHierName(processor), program);
    }

    return processor;
}

static optModuleP root = NULL;

Uns32 addressBits = 32;

static void root_create(const char *args) {
    opSessionInit(OP_VERSION);
    optCmdParserP parser = opCmdParserNew(SHELL_NAME, OP_AC_EXT1);

    opCmdParserAdd (parser, "addressbits", 0, 0, "platform", OP_FT_INT32VAL,
        &addressBits, "Number of bits on address bus (default=32)",OP_AC_ALL, 0, 0);

    char *fname = "OVP_AUTO.ic";
    FILE *fp = fopen(fname, "w");
    fprintf(fp, "# Auto-Generated\n");
    if (args) {
        fprintf(fp, "%s", args);
    }
    fclose(fp);
    opCmdParseFile(parser, fname);
    remove(fname);

    // look for a specific finishafter
    char *marker;
    if ((marker=strstr(args, "--finishafter"))) {
        marker += strlen("--finishafter");
        Uns64 count = 1000000;
        sscanf(marker, "%lu", (long unsigned int *)&count);
        svState[0].finishafter = count;
    }

    optParamP pl = NULL;
    pl = opParamBoolSet(pl, OP_FP_VERBOSE, True);
    pl = opParamBoolSet(pl, OP_FP_STOPONCONTROLC, True);
    pl = opParamBoolSet(pl, OP_FP_SYSTEMVERILOG,  True);

    root = opRootModuleNew(0, "root", pl);
}

//
// Retrieve SystemVerilog State to OVP
//
static void cpu_getState(int id) {
    getState(
        &(svState[id].terminate.value),
        &(svState[id].reset.value),
        &(svState[id].nmi.value),
        &(svState[id].MSWInterrupt.value),
        &(svState[id].USWInterrupt.value),
        &(svState[id].SSWInterrupt.value),
        &(svState[id].MTimerInterrupt.value),
        &(svState[id].UTimerInterrupt.value),
        &(svState[id].STimerInterrupt.value),
        &(svState[id].MExternalInterrupt.value),
        &(svState[id].UExternalInterrupt.value),
        &(svState[id].SExternalInterrupt.value)
    );

    opNetWrite(svState[id].reset.net,              svState[id].reset.value);
    opNetWrite(svState[id].nmi.net,                svState[id].nmi.value);

    opNetWrite(svState[id].MSWInterrupt.net,       svState[id].MSWInterrupt.value);
    opNetWrite(svState[id].USWInterrupt.net,       svState[id].USWInterrupt.value);
    opNetWrite(svState[id].SSWInterrupt.net,       svState[id].SSWInterrupt.value);

    opNetWrite(svState[id].MTimerInterrupt.net,    svState[id].MTimerInterrupt.value);
    opNetWrite(svState[id].UTimerInterrupt.net,    svState[id].UTimerInterrupt.value);
    opNetWrite(svState[id].STimerInterrupt.net,    svState[id].STimerInterrupt.value);

    opNetWrite(svState[id].MExternalInterrupt.net, svState[id].MSWInterrupt.value);
    opNetWrite(svState[id].UExternalInterrupt.net, svState[id].UExternalInterrupt.value);
    opNetWrite(svState[id].SExternalInterrupt.net, svState[id].SExternalInterrupt.value);
}

//
// Pass OVP State to SystemVerilog
//
static void cpu_putState(int id) {
    Uns64 buffer;
    Int32 regid;
    optRegP reg;
    optRegGroupP grp;
    Bool ok;

    optProcessorP processor = svState[id].processor;

    // Get the GPR's
    grp = opProcessorRegGroupByName(processor, "Core");
    regid = 0; reg = 0;
    while(grp && (reg = opRegGroupRegNext(processor, grp, reg))) {
        buffer = 0;
        ok = opProcessorRegRead(processor, reg, &buffer);
        if (ok) {
            if (regid<32) {
                // Conditional update
                if (buffer != svState[id].gpr[regid]) {
                    setGPR(regid, buffer);
                    svState[id].gpr[regid] = buffer;
                }
            } else {
                // This is the PC
                setPC(buffer);
            }
        }
        regid++;
    }

    // Get the FPR's
    grp = opProcessorRegGroupByName(processor, "Floating_point");
    regid = 0; reg = 0;
    while(grp && (reg = opRegGroupRegNext(processor, grp, reg))) {
        buffer = 0;
        ok = opProcessorRegRead(processor, reg, &buffer);
        if (ok) {
            if (regid<32) {
                // Conditional update
                if (buffer != svState[id].fpr[regid]) {
                    setFPR(regid, buffer);
                    svState[id].fpr[regid] = buffer;
                }
            } else {
                break;
            }
        }
        regid++;
    }

    // Todo Get the Vector's

    // Get the CSR's ignore cycle instret
    grp = opProcessorRegGroupByName(processor, "Machine_Control_and_Status");
    regid = 0; reg = 0;
    while(grp && (reg = opRegGroupRegNext(processor, grp, reg))) {
        buffer = 0;
        ok = opProcessorRegRead(processor, reg, &buffer);
        if (ok) {
            if (regid<4096) {
                if (buffer != svState[id].mcsr[regid]) {
                    const char *name = opRegName(reg);
                    if (!strcmp("mcycle", name) || !strcmp("minstret", name)) {
                    } else {
                        setCSR(name, buffer);
                        svState[id].mcsr[regid] = buffer;
                    }
                }
            }
        }
        regid++;
    }

    grp = opProcessorRegGroupByName(processor, "User_Control_and_Status");
    regid = 0; reg = 0;
    while(grp && (reg = opRegGroupRegNext(processor, grp, reg))) {
        buffer = 0;
        ok = opProcessorRegRead(processor, reg, &buffer);
        if (ok) {
            if (regid<4096) {
                if (buffer != svState[id].ucsr[regid]) {
                    const char *name = opRegName(reg);
                    if (!strcmp("cycle", name) || !strcmp("instret", name)) {
                    } else {
                        setCSR(name, buffer);
                        svState[id].ucsr[regid] = buffer;
                    }
                }
            }
        }
        regid++;
    }

    grp = opProcessorRegGroupByName(processor, "Supervisor_Control_and_Status");
    regid = 0; reg = 0;
    while(grp && (reg = opRegGroupRegNext(processor, grp, reg))) {
        buffer = 0;
        ok = opProcessorRegRead(processor, reg, &buffer);
        if (ok) {
            if (regid<4096) {
                if (buffer != svState[id].scsr[regid]) {
                    const char *name = opRegName(reg);
                    setCSR(name, buffer);
                    svState[id].scsr[regid] = buffer;
                }
            }
        }
        regid++;
    }
}

Bool stopSimulation(optStopReason stopreason) {
    if (stopreason == OP_SR_SCHED) {
        return False;
    }

    opPrintf("Stopping Simulation Reason=%d\n", stopreason);
    return True;
}

/*
 * The busWait function stops execution from the CPU perspective
 * until told to step by SV
 *
 * The fetch/read/write callbacks will then execute
 * The State is updated
 * The Retire event flag is set
 */
int cpu_init(int id, const char *args, const char *vendor, const char *variant, const char *program, int save_state) {
    if (!root) {
        svState[0].finishafter = 1000000; // Default 1 Million
        root_create(args);
    }

    svState[id].processor   = cpu_create(root, id, vendor, variant, addressBits, program);
    optProcessorP processor = svState[id].processor;

    int first = 1;
    optStopReason stopreason = OP_SR_SCHED;
    while (1) {
        if (first) {
            first = 0;

            // await all processor instantiations
            busWait();
            opRootModulePreSimulate(root);
            if (save_state) {
                cpu_putState(id);
            }
        }
        svState[id].icount++;

        // Instruction to be Executed
        const char *decode = opProcessorDisassemble(processor, opProcessorPC(processor), OP_DSA_UNCOOKED);
        setDECODE(decode);

        // Execute
        stopreason = opProcessorSimulate(processor, 1);

        if (stopreason!=OP_SR_SCHED) {
            if (stopreason==OP_SR_EXIT || stopreason==OP_SR_FINISH) {
                // Termination for Imperas Perspective
                opSessionTerminate();
                return 0;
            } else {
                busWait();
            }
        }

        // State after Execution
        if (save_state) {
            cpu_putState(id);
        }

        // indicate completion of instruction transactions
        setRETIRE();

        // Get any input changes
        cpu_getState(id);

        // check for termination via the verilog bus, or finishafter
        if (svState[id].terminate.value || (svState[id].icount >= svState[0].finishafter)) {
            opSessionTerminate();
            return 0;
        }
    }
    return 0;
}

/*
 * Explictly call opSessionTerminate
 * TODO: do something intelligent with "id"
 *
 */
int cpu_term(int id, const char *caller) {
    printf("[RISCV_SV INFO]: Explicit termination called by %s\n", caller);
    //printf("[RISCV_SV INFO]: Explicit termination\n");
    opSessionTerminate();
    return 0;
}

int cpu_disass(int id, const char **str) {
    optProcessorP processor = svState[id].processor;

    if(!processor)
        opMessage("F", SHELL_NAME, "No Processor Found");

    *str = opProcessorDisassemble(processor, opProcessorPC(processor), OP_DSA_BASE);
    return 0;
}


