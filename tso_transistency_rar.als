module RAR

/** Memory addresses for TLB or payload references */
sig Address {}

enum Bool { True, False }

/** RAR Status codes: 0x00=SUCCESS, 0x01=PENDING, 0x80=FAILURE. */
enum RARStatus { SUCCESS, PENDING, FAILURE }

enum PayloadType {
  PAGE_INV, 
  PAGE_INV_NO_CR3,
  PCID_INV,
  EPT_INV,
  VPID_INV,
  MSR_WRITE
}

enum SubType { ADDRESS_SPECIFIC, ALL_CONTEXT }

/** 
 * CPU Execution States
 * SMM and WAIT_FOR_SIPI inhibits RAR
 */
enum CPUExecState {
  NORMAL, // Normal
  INIT,   // RAR is cleared if in INIT
  SMM, 
  WAIT_FOR_SIPI,
  SHUTDOWN,
  C6_SLEEP, // SLEEP
  BIOS_GUARD,
  SGX_ENCLAVE // SGX State
}

/** Action Vector */
sig RARAction {
  idx: Int,
  status: one RARStatus
}

/** PayloadTableEntry */
sig PayloadTableEntry {
  pType: one PayloadType,
  pSubType: lone SubType,
  linearAddr: lone Address,
  cr3bits, pcidbits, vpidbits, eptbits, msrData: Int,
  idxInTable: Int
}

/** RAR_INFO MSR */
sig RAR_INFO_MSR {
  tableMaxIndex: Int
}

sig RAR_CONTROL_MSR {
  enable: one Bool,    // bit31
  ignoreIF: one Bool   // bit30
}

sig RAR_ACTION_VECTOR_MSR {
  vectorAddr: Int
}

sig RAR_PAYLOAD_TABLE_BASE_MSR {
  tableBase: Int
}

/** 
 * IA32_CORE_CAPABILITIES with a rarBit => means RAR enumerated or not
 */
sig IA32_CORE_CAPABILITIES {
  rarBit: one Bool
}

/** 
 * Each Processor has references to the RAR MSRs, plus TLB, plus a set of RARAction entries
 * Also tracks whether the OS allocated memory
 */
sig Processor {
  coreCaps: one IA32_CORE_CAPABILITIES,
  msrControl: one RAR_CONTROL_MSR,
  msrInfo: one RAR_INFO_MSR,
  msrActionVector: one RAR_ACTION_VECTOR_MSR,
  msrTableBase: one RAR_PAYLOAD_TABLE_BASE_MSR,

  execState: one CPUExecState,

  cr3, pcid, vpid: Int,

  tlb: set Address,

  actionVec: set RARAction,

  // Some booleans about OS setup:
  allocatedTable: one Bool,
  allocatedVector: one Bool,
  msrsProgrammed: one Bool,

  // EFLAGS.IF. If ignoreIF= false => must have IF= true for RAR to proceed
  IF: one Bool
}

/** 
 * A RAR event signaled by writing to the ICR with deliveryMode=0b011. 
 */
abstract sig Event {}
sig RAR extends Event {
  target: one Processor, // CPU
  usedIndex: Int
}

/** --------- 1.3, 2.3 OS Setup & Detection/Enabling --------- */

fact OS_SetupAndEnable {
  all p: Processor {
    // If rarBit= False => CPU cannot enable RAR
    (p.coreCaps.rarBit = False) => (p.msrControl.enable = False)

    // If OS wants to enable RAR => must allocate memory for table & vector
    (p.msrControl.enable = True) => (p.allocatedTable = True and p.allocatedVector = True)

    // If RAR is enabled => OS must have “programmed” the addresses
    (p.msrControl.enable = True) => p.msrsProgrammed = True
  }
}

/** If CPU doesn’t have RAR enumerated => no RAR
    If enumerated but not enabled => any RAR is effectively not serviced => no r */
fact RAR_EnableCheck {
  all r: RAR |
    r.target.msrControl.enable = True
    or no r
}

/** --------- 3. Signaling a Remote Action Request --------- */

/** skip ICR details -- if RAR is signaled => we have a RAR object
    Must require that rarBit= True to exist. */
fact RAR_Signaling {
  all r: RAR |
    (r.target.coreCaps.rarBit= True)
    or no r
}

/** --------- 5. Action Vector & Payload Table --------- */

/** Global set for entries 
In a real model, each CPU might have its own table */
sig PayloadTableEntryGlobal in PayloadTableEntry {}

/** #actionVec <= tableMaxIndex+1. */
fact ActionVectorSize {
  all p: Processor |
    #p.actionVec <= (p.msrInfo.tableMaxIndex + 1)
}

/** Each payload entry must have idxInTable < tableMaxIndex+1
  only a partial check globally. */
fact PayloadTableSize {
  all e: PayloadTableEntryGlobal, p: Processor |
    e.idxInTable < (p.msrInfo.tableMaxIndex + 1)
}

/** --------- 7. RLP Remote Action Request Handling --------- */

/** 
 *  RAR only serviced if msrControl.enable= True
 * If ignoreIF=0 => IF must be=1
 * For each action j that is PENDING => ,read the payload
 *  skipped actual membership checking (i.e. e.pType in supportedTypes)
 */
fact RLPHandlingFlow {
  // If not enabled => the RAR is ignored
  // If ignoreIF= false => IF= true
  all r: RAR {
    let p = r.target |
      (p.msrControl.enable = True) => {
        (p.msrControl.ignoreIF= True) or (p.IF= True)
      }
  }

  // For each PENDING action => must find some table entry with matching idx, 
  // then presumably success or fail
  // skipped the “in supportedTypes” check
  all p: Processor, a: p.actionVec |
    a.status= PENDING => {
      some e: PayloadTableEntryGlobal | e.idxInTable= a.idx
    }
}

/** 8.1 Priority vs. intr: done above. */
/** 8.2 Sleep states: if CPU= C6_SLEEP => no RAR or no effect */
fact SleepStateInhibit {
  all r: RAR |
    r.target.execState = C6_SLEEP => no r
}

/** 8.3 skip SGX
  Partially check suppose enclaves if address in EnclaveRange => possible AEX */
sig EnclaveRange in Address {}
fact RAR_SGX {
  // If p=SGX_ENCLAVE and e in EnclaveRange => AEX. We'll just do no constraints to avoid warnings.
  no none
}

/** 8.4 RAR Clear Conditions: If CPU=INIT => RAR pending is cleared => no RAR */
fact RARClearedOnINIT {
  all r: RAR |
    r.target.execState = INIT => no r
}

/** 8.5 Inhibit states: SMM, WAIT_FOR_SIPI, SHUTDOWN, BIOS_GUARD => no RAR. */
fact RARInhibitStates {
  all r: RAR |
    r.target.execState in SMM + WAIT_FOR_SIPI + SHUTDOWN + BIOS_GUARD => no r
}

/** 8.6 skips advanced EPT/GPA details. */

pred showExample {}
run showExample for 6
