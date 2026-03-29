# Certior Debugger Architecture

**Formal Agent Language & Verification Engine**  
This document outlines the architecture of the Certior Debugger, a purely formal execution environment for autonomous agents, written in Lean 4. 

---

## Core Philosophy

Standard debuggers execute code interactively. The Certior Debugger uses mathematical theorem proving to verify code logic against an internal compliance lattice *before* determining if a step is legally permitted to execute. It acts as an interactive bridge between VS Code's Debug Adapter Protocol (DAP) and the Lean 4 kernel.

---

## System Architecture

### 1. `Session.lean` — The Evaluation Engine
The core of the debugger is `PlanDebugSession`. It manages absolute verification states throughout the execution process.

- **Verification Breakpoints:** Unlike standard debuggers that only break on specific lines of code, Certior implements logic-based breakpoints:
  - **Flow Breakpoints:** Automatically halts execution if an entity attempts to observe data tagged with a sensitivity level higher than its authorization tier.
  - **Budget Breakpoints:** Halts if the execution step is mathematically guaranteed to exceed the allocated computational or API budget.
  - **Capability Breakpoints:** Triggers if an execution plan attempts an I/O operation missing a mathematically verified capability certificate.
- **Time-Travel Debugging:** maintains a complete, forward-and-backward verifiable execution trace history array, allowing compliance auditors to rewind execution steps losslessly.

### 2. `Core.lean` — The 4-Scope DAP Translation Layer
To expose Lean 4's formal theorems to the standard VS Code interface, we implement a custom 4-scope encoding pattern mapping DAP frame requests.

Standard debuggers map stack frames to `locals` and `globals`. Certior maps each stack frame identically to four specific security vectors:
1. **Locals:** Standard variable and binding environments.
2. **Resources:** The agent's strict resource allowance limits (API limits, memory constraints).
3. **Flow Labels:** The calculated mathematical sensitivity context (e.g. `Public`, `Internal`, `Restricted`) for the active operation.
4. **Certificates:** Live generation of proof certificates demonstrating cryptographic evidence that the current state is compliant.

### 3. Verification Translation Pipeline

```text
┌──────────────────────────────────────────────────────┐
│              VS Code / DAP Client                    │
└──────────┬──────────────┬───────────────┬────────────┘
           │              │               │
           ▼              ▼               ▼
┌──────────────────────────────────────────────────────┐
│  Core.lean — SessionStore + 4-Scope DAP API          │
│                                                      │
│  Scope encoding: frameId * 4 + {1,2,3,4}             │
│  Custom queries: Certificates, Flow Lattices         │
└──────────────────────┬───────────────────────────────┘
                       │
                       ▼
┌──────────────────────────────────────────────────────┐
│  Session.lean — CertiorDebugSession                  │
│                                                      │
│  Verification Triggers: logic → flow → budget        │
└──────────────────────┬───────────────────────────────┘
                       │
                       ▼
┌──────────────────────────────────────────────────────┐
│  Eval.lean — Verify-Before-Step Interpreter          │
│  capabilityCheck → budgetCheck → flowCheck → execute │
│  Backing formal logic: CertiorLattice.levelCanFlowTo │
└──────────────────────────────────────────────────────┘
```

---

## Testing & Compilation Coverage

The debugger's internal formal consistency is enforced through extensive automated proofs covering the AST interpretation and evaluation layers.

### Run Local Compilation
To compile the debugger and run the formal test suite locally:

```bash
git clone https://github.com/certior/certior-debugger.git
cd certior-debugger/CertiorPlan
lake build
lake exe plan-tests
```
