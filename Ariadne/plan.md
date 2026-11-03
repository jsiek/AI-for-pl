# Verification Blueprint: AI-Driven PCC Pipeline for C Heap Data Structures

## 1. Core Architecture & Verification Goals
This blueprint details the engineering requirements for an AI-driven, Proof-Carrying Code (PCC) verification workflow. The pipeline validates **absolute memory safety** of pointer-dense C programs.

*   **Primary Objective:** Automate verification of intricate heap properties (absence of buffer overflows, invalid pointer dereferences, uninitialized reads, and use-after-free conditions).
*   **Verification Strategy:** Deductive verification using Weakest Precondition (WP) calculus.
*   **Target Guarantee:** Emission of a compiled mathematical proof object (Safety Certificate) that can be verified by an independent third-party type checker in deterministic, near-linear time relative to program size.

---

## 2. Technical Stack Configuration

The execution pipeline combines static analysis, interactive theorem proving, and an automation wrapper:

*   **Front-End Specification & Instrumentation:** [Frama-C](https://frama-c.com/) (Version 31.0+ Gallium) equipped with **RTE** (Runtime Error generation) and **Eva** (Evolved Value Analysis) plugins.
*   **Logical Property Language:** ANSI/ISO C Specification Language (ACSL).
*   **Back-End Deductive Engine:** Frama-C **WP Plugin** routed through the **Why3 platform**.
*   **Interactive Target Environment:** [Coq / Rocq](https://coq.inria.fr/) proof assistant.
*   **Automation Suite:** **CoqHammer** (integrated into the Coq workspace) to resolve minor arithmetic and algebraic sub-goals.
*   **Agent Automation Interface:** **Python 3.11+** running an asynchronous loop, communicating with Coq via the `coq-lsp` server protocol over JSON-RPC.

---

## 3. Sandboxed Agent Execution Loop

The implementation script must orchestrate a stateful loop allowing the AI agent to incrementally construct the code specifications and proof scripts.

```
       [ Input C Source Code File ]
                   │
                   ▼
    ┌───► [ Frama-C CLI Processing ]
    │              │
    │              ▼ (Translates code + ACSL via Why3)
    │     [ Coq Goal Files (.v) ]
    │              │
    │              ▼
    │     [ Agent Interaction Loop via coq-lsp ] ───► (Applies tactics: hammer, induction...)
    │              │
    │              ├─► SUCCESS: Compiles to `.vo` Certificate
    │              │
    │              └─► FAILURE: Invariant/Assertion too weak
    │                      │
    └──────────────────────┴───► [ Agent rewrites C / ACSL source ]
```

### Script Operational Steps:
1.  **Instrument with RTE:** Run `frama-c -rte your_code.c -code-shaping` to generate baseline memory access properties (`alid`, `alid_read`).
2.  **Run Eva Analysis:** Use abstract interpretation to compute memory intervals and points-to sets, serving as base hypotheses.
3.  **Generate Coq Export:** Target WP to Coq via `frama-c -wp -wp-prover coq -wp-timeout 20 your_code.c`. This populates the `.v` goals.
4.  **Execute Proof Tactic Loop:** The Python agent opens the `.v` files via `coq-lsp`, querying goal states. It pushes structural tactics (`induction`, `inversion`, `intros`) and utilizes `hammer.` to finalize leaf goals.
5.  **Handling Proof Stalls (Dynamic Refinement):** If a sub-goal is unprovable due to a missing invariant, the agent must drop back to the C level, inject a helper assertion (`/*@ assert ... */`) or a generalized `/*@ loop invariant ... */`, and re-trigger step 1.

---

## 4. Case Study: Sglib (Simple Generic Library)

The target codebase for evaluation is [sglib](https://github.com/Marian-Vittek/sglib), a header-only generic library for handling intrusive C containers.

### Why Sglib is the Target Testbed:
*   **Pure Memory Complexity:** It implements complex heap topologies (**Red-Black Trees, Doubly Linked Lists, Hash Containers**) completely detached from system bindings.
*   **Intrusive Architectures:** Pointers links are stored directly inside user structures. This requires the verification model to constantly handle custom aliasing, boundary layouts, and complex struct typecasting.
*   **The Mathematical Moat:** Standard automated first-order SMT solvers fail instantly on these recursive pointer configurations. They must be resolved inductively via Coq.

### Reference Code Templates for Workflow Development

To bootstrap the evaluation engine, use the official sample files included in the `sglib/samples` distribution directory as verification benchmarks:

#### Benchmark 1: Intrusive Doubly Linked List Validation (`dllist.c`)
Demonstrates how user structs link dynamically. The AI agent must verify that traversals do not cause null pointer dereferences or unmapped memory indexing.

```c
#include <stdio.h>
#include <stdlib.h>
#include "sglib.h"

typedef struct ilist {
    int value;
    struct ilist *next;
    struct ilist *previous;
} ilist;

/* Define Level 1 interfaces for the Doubly Linked List */
SGLIB_DEFINE_DL_LIST_PROTOTYPES(ilist, next, previous);
SGLIB_DEFINE_DL_LIST_FUNCTIONS(ilist, next, previous);

int main() {
    ilist *list = NULL;
    ilist *e;
    
    // Test fixture allocation
    for (int i = 0; i < 5; i++) {
        e = malloc(sizeof(ilist));
        if (e == NULL) return 1;
        e->value = i * 10;
        SGLIB_DL_LIST_ADD(ilist, list, e, next, previous);
    }
    
    // The verification target must prove that iteration via macros is memory safe
    struct ilist *iterator;
    SGLIB_DL_LIST_FOR_EACH(ilist, list, iterator, next, previous) {
        printf("Value: %d\n", iterator->value);
    }
    
    return 0;
}
```

#### Benchmark 2: Complex Heap Logic - Red-Black Tree (`rbtree.c`)
The absolute stress-test for the agent. Validating an insert or rebalance loop requires advanced functional contracts mapping node coloration and invariant shape balancing.

```c
#include <stdio.h>
#include <stdlib.h>
#include "sglib.h"

typedef struct node {
    int key;
    char color;
    struct node *left;
    struct node *right;
} node;

// Define comparator function macro required by sglib
#define CMP_NODES(x, y) ((x)->key - (y)->key)

SGLIB_DEFINE_RBTREE_PROTOTYPES(node, left, right, color, CMP_NODES);
SGLIB_DEFINE_RBTREE_FUNCTIONS(node, left, right, color, CMP_NODES);

int main() {
    node *tree = NULL;
    node *n = malloc(sizeof(node));
    if (n == NULL) return 1;
    n->key = 42;
    
    SGLIB_RBTREE_ADD(node, tree, n, left, right, color, CMP_NODES);
    
    node tmp;
    tmp.key = 42;
    node *found = SGLIB_RBTREE_FIND(node, tree, &tmp, left, right, CMP_NODES);
    
    if (found != NULL) {
        printf("Found key: %d\n", found->key);
    }
    return 0;
}
```

---

## 5. Security Guardrails & Cryptographic Proof Verification

Because the AI agent is given permission to write and adjust annotations, the pipeline enforces an absolute validation mechanism:

1.  **Isolation of Assertions:** Any helper assertion `/*@ assert P; */` injected by the agent generates split sub-goals. The framework explicitly blocks the agent from passing an unproven lemma down the pipeline; it *must* prove that `P` is valid given previous states before using it as a hypothesis.
2.  **Zero-Trust Engine:** The AI agent's internal operations do not form any part of the trust root. The only asset outputted from the script is the `.vo` object.
3.  **The Certificate Checker:** The validation environment invokes Coq's micro-kernel type checker:
    ```bash
    coqchk -o your_proof_module.vo
    ```
    If `coqchk` compiles successfully, the C program is cryptographically certified as safe. The validation runs deterministically without using heuristics or infinite search bounds, achieving near-linear validation latency.
