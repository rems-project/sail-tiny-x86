$include <concurrency_interface.sail>
$include <concurrency_interface/tlbi.sail>
$include <concurrency_interface/exception.sail>
$include <concurrency_interface/cache_op.sail>
$include <concurrency_interface/translation.sail>

/* 
   This interface depends on a few parameters:
   - mem_acc : Type, An architecture specific description of the access kind.
     This may also contain arbitrary architecture specific metadata about the
     access.
   - CHERI : Bool, Whether CHERI is active on this architecture, which means the
     memory has capability tags
   - cap_size_log : Int, If CHERI is on, the log2 of the size of capabilities in
     bytes. For example for 16 bytes capabilities, this should be 4.
*/

// addr_size : Int, The size of addresses to be used, in bits
type addr_size : Int = 64
let addr_size' : int(64) = 64

/*
addr_space : Type, An extra tag on the address to identify its address
     space. For Arm this is Secure/Non-Secure, for all other architecture this
     should probably be unit.
*/
type addr_space : Type = unit
let addr_space_def = ()

/*
abort : Type, The type of memory aborts/access failure: To be
     returned when the access has failed. In system-level instantiations, this is
     expected to be for physical memory abort (e.g. SError in Arm)

Using a generic name 'Fault' as implementing a simplified memory model
*/
enum Fault = {
    // see 6.5.1 Call and Return Operation for Interrupt or Exception Handling Procedures (Intel manual)
    Fault_DB, // Debug
    Fault_NMI, // Non-maskable interrupt
    Fault_DF, // Double Fault
    Fault_NP, // Segment Not Present
    Fault_SS, // Stack Segment Fault
    Fault_GP, // General Protection
    Fault_PF, // Page Fault
    Fault_AC, // Alignment Check
    Fault_MC, // Machine Check
    Fault_CP, // Control Protection Exceptiobn
}
type abort: Type = Fault