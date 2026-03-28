<p align="center">
  <img src="https://raw.githubusercontent.com/certior/boxclaw/main/assets/logo.svg" width="200" alt="Certior Glassbox">
</p>

<h1 align="center">Certior Debugger</h1>

<p align="center">
  <strong>Formally Verified AI Agent Debugger for VS Code (Built on Lean 4)</strong>
</p>

<p align="center">
  <a href="#installation">Installation</a> •
  <a href="#the-problem">The Problem</a> •
  <a href="#features">Features</a> •
  <a href="#quick-start">Quick Start</a>
</p>

---

## The Problem
Autonomous AI agents are incredibly powerful, but they operate as **black boxes**. To deploy them in high-risk, high-compliance environments (Healthcare, Finance, Government), you cannot just blindly trust an LLM prompt. You need absolute, mathematically verifiable guarantees that an AI will not leak data, compromise security, or execute unauthorized code.

## The Solution
**Certior Debugger** is a groundbreaking IDE extension that uses mathematical theorem proving (via **Lean 4**) to formally verify AI execution plans *before* they run. It acts as an interactive debugger for your agent's logic. If an agent tries to pass a HIPAA-protected patient record to an unauthorized public API, Certior will mathematically prove that the flow is illegal and halt the execution.

## Features
- **🔬 Mathematical Verification:** Uses the formal logic of Lean 4 to evaluate an agent's execution sequence.
- **🛡️ Custom Compliance Policies:** Test your agent against built-in policies (HIPAA, SOX, Default) or define your own Zero-Trust lattices.
- **⚡ Step-Through Debugging:** Visually step through an AI's autonomous plan right inside VS Code.
- **📜 Proof Certificates:** Generate cryptographic proof certificates demonstrating that a given AI plan is mathematically sound and compliant.

## Installation

You do not need to be a Lean 4 expert to use this tool! We have packaged it as a ready-to-use VS Code extension.

1. **Prerequisite:** Install [Lean 4](https://leanprover-community.github.io/get_started.html) on your system.
2. Download the latest `.vsix` extension from this repository: [`vscode-extension/certior-plan-dap-client-0.1.0.vsix`](vscode-extension/certior-plan-dap-client-0.1.0.vsix).
3. Open **VS Code**.
4. Go to the Extensions panel on the left (`Ctrl+Shift+X` / `Cmd+Shift+X`).
5. Click the `...` menu in the top right of the panel and select **"Install from VSIX..."**
6. Select the downloaded `certior-plan-dap-client-0.1.0.vsix` file.

## Quick Start (3-Minute Demo)

1. Open the `CertiorPlan` folder in VS Code.
2. Navigate to one of our pre-built examples: `examples/HIPAAIntegrationDemo.lean`
3. Press `F5` to open the **Run and Debug** panel.
4. Select **Certior HIPAA Debug** from the dropdown and hit the Play button.
5. In the Debug Console, you will see the mathematical verification process evaluate step-by-step.
   - *If the plan is safe*: You will receive a successful Proof Certificate.
   - *If the plan violates the lattice*: The debugger will isolate the exact node where the data leak occurred.

This allows developers to securely audit AI behaviors locally, bridging the gap between cutting-edge LLMs and mission-critical enterprise compliance.
