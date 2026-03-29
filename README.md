<p align="center">
  <img src="https://raw.githubusercontent.com/certior/boxclaw/main/assets/logo.svg" width="200" alt="Certior Logo">
</p>

<h1 align="center">Certior Debugger</h1>

<p align="center">
  <strong>Formally Verified AI Agent Debugger for VS Code (Built on Lean 4)</strong>
</p>

<p align="center">
  <img src="verification-explorer.gif" alt="Certior Verification Explorer UI" width="700">
</p>

<p align="center">
  <a href="#installation">Installation</a> •
  <a href="#the-problem">The Problem</a> •
  <a href="#features">Features</a> •
  <a href="#quick-start--ui-guide">Quick Start</a> •
  <a href="CertiorPlan/ARCHITECTURE.md">Architecture</a>
</p>

---

## The Problem
Autonomous AI agents are powerful, but they operate as **black boxes**. To deploy them in high-risk, high-compliance environments (Healthcare, Finance, Government), you cannot just blindly trust an LLM prompt. You need absolute, mathematically verifiable guarantees that an AI will not leak data, compromise security, or execute unauthorized code.

## The Solution
**Certior Debugger** is an IDE extension that uses mathematical theorem proving (via **Lean 4**) to formally verify AI execution plans *before* they run. It acts as an interactive debugger for your agent's logic. If an agent tries to pass a HIPAA-protected patient record to an unauthorized public API, Certior will mathematically prove that the flow is illegal and halt the execution.

## Features
- **🔬 Mathematical Verification:** Uses the formal logic of Lean 4 to evaluate an agent's execution sequence.
- **🛡️ Custom Compliance Policies:** Test your agent against built-in policies (HIPAA, SOX, Default) or define your own Zero-Trust lattices.
- **⚡ Step-Through Debugging:** Visually replay and step through an AI's autonomous execution trace inside VS Code's InfoView Widget.
- **📜 Proof Certificates:** Generate cryptographic proof certificates demonstrating that a given execution phase is mathematically sound.

## Installation

You do not need to be a Lean 4 expert to use this tool! We have packaged it as a ready-to-use VS Code extension.

1. **Prerequisite:** Install [Lean 4](https://leanprover-community.github.io/get_started.html) on your system.
2. Download the latest `.vsix` extension from this repository: [`vscode-extension/certior-plan-dap-client-0.1.0.vsix`](vscode-extension/certior-plan-dap-client-0.1.0.vsix).
3. Open **VS Code**.
4. Go to the Extensions panel on the left (`Ctrl+Shift+X` / `Cmd+Shift+X`).
5. Click the `...` menu in the top right of the panel and select **"Install from VSIX..."**
6. Select the downloaded `certior-plan-dap-client-0.1.0.vsix` file.

## Quick Start & UI Guide
1. Open the `CertiorPlan` folder in VS Code.
2. Navigate to one of our pre-built examples: `examples/HIPAAIntegrationDemo.lean`
3. Click on the `#widget CertiorPlan.verificationExplorerWidget` line in the code to place your cursor on it.
4. Open the **Lean InfoView** panel (`Ctrl+Shift+Enter` / `Cmd+Shift+Enter`). You will see the **Certior Verification Explorer**.

### Navigating the UI
- **Playback Controls:** Click **Step Forward** to advance the agent's execution sequence one node at a time. You can also use **< Back** to reverse or **▶ Run to End** to fast-forward. The active node traversing the plan will be highlighted in blue.
- **State Tab:** View the current memory state, variable bindings, and compliance budget remaining at each exact execution tick.
- **Certificates Tab:** Shows the cryptographically signed Lean proofs verifying that the current operation complies with the Zero-Trust lattice policies.
- **Halting on Violations:**
  - *Safe Plan:* You will step through to completion.
  - *Violating Plan:* As soon as an illegal action is attempted (e.g. data leak), the node turns red (`flow_violation`), the proof certificates explicitly outline the failed rank comparison, and playback controls are automatically locked out to statically prevent the harmful operation.

This visual interface allows developers to securely audit AI behaviors locally, bridging the gap between cutting-edge LLMs and mission-critical enterprise compliance.
