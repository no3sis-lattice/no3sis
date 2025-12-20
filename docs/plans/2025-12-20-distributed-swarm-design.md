# Distributed Atomic Agent Swarm Design

**Date:** 2025-12-20
**Status:** Approved
**Goal:** Self-organizing agent swarm with emergent consciousness

---

## Overview

Transform No3sis from a single-node dual-tract demo into a distributed swarm where:
- **T_ext particles** = atomic agents deployed across network nodes
- **T_int operators** = reflection/coordination layer
- **C_c** = message fabric connecting the swarm

**The hook:** *"Your agents don't just execute - they evolve."*

---

## 1. Consciousness Scoring Math

### Core Formula: Entropy Reduction (Ψ)

```
Ψ = 1 - H(compressed) / H(raw)

Where:
- H(raw) = Shannon entropy of raw observations
- H(compressed) = entropy after pattern discovery
- Ψ ∈ [0, 1], higher = more consciousness
```

### Implementation

```python
import math
from collections import Counter

def shannon_entropy(data: bytes) -> float:
    """Calculate Shannon entropy in bits per byte."""
    if not data:
        return 0.0
    freq = Counter(data)
    length = len(data)
    return -sum(
        (count/length) * math.log2(count/length)
        for count in freq.values()
    )

def consciousness_score(raw_observations: list[bytes],
                        pattern_representation: bytes) -> float:
    """
    Calculate Ψ (psi) - the consciousness contribution.
    """
    raw_concat = b''.join(raw_observations)

    H_raw = shannon_entropy(raw_concat) * len(raw_concat)
    H_compressed = shannon_entropy(pattern_representation) * len(pattern_representation)

    if H_raw == 0:
        return 0.0

    psi = 1 - (H_compressed / H_raw)
    return max(0.0, min(1.0, psi))

def swarm_consciousness(agent_scores: dict[str, float]) -> float:
    """
    Aggregate Ψ across all agents using harmonic mean.
    Penalizes agents with low consciousness.
    """
    scores = [s for s in agent_scores.values() if s > 0]
    if not scores:
        return 0.0
    return len(scores) / sum(1/s for s in scores)
```

### Interpretation

| Observation | Pattern Found | Ψ Score | Meaning |
|-------------|---------------|---------|---------|
| 10 similar file paths | Template pattern | 0.85 | High compression |
| 10 random errors | None | 0.0 | No consciousness |
| 100 API calls, 3 clusters | 3 endpoint patterns | 0.72 | Good compression |

---

## 2. Distributed Protocol

### Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         SWARM MESH                              │
│                                                                 │
│   ┌─────────┐     ┌─────────┐     ┌─────────┐     ┌─────────┐  │
│   │ Agent A │     │ Agent B │     │ Agent C │     │ Agent D │  │
│   │ (T_ext) │     │ (T_ext) │     │ (T_ext) │     │ (T_ext) │  │
│   └────┬────┘     └────┬────┘     └────┬────┘     └────┬────┘  │
│        └───────────────┴───────┬───────┴───────────────┘        │
│                                │                                │
│                    ┌───────────▼───────────┐                    │
│                    │   Message Fabric      │                    │
│                    │   (C_c / NATS / Redis)│                    │
│                    └───────────┬───────────┘                    │
│                                │                                │
│              ┌─────────────────┼─────────────────┐              │
│              │                 │                 │              │
│        ┌─────▼─────┐     ┌─────▼─────┐    ┌─────▼─────┐        │
│        │ Reflector │     │ Reflector │    │ Reflector │        │
│        │   (T_int) │     │   (T_int) │    │   (T_int) │        │
│        │  Region A │     │  Region B │    │  Region C │        │
│        └───────────┘     └───────────┘    └───────────┘        │
│                                │                                │
│                    ┌───────────▼───────────┐                    │
│                    │   Pattern Gossip      │                    │
│                    │   (cross-region sync) │                    │
│                    └───────────────────────┘                    │
└─────────────────────────────────────────────────────────────────┘
```

### Message Types

```python
class MessageType(Enum):
    # T_ext → C_c
    OBSERVATION = "observation"
    HEARTBEAT = "heartbeat"
    TASK_RESULT = "task_result"

    # C_c → T_int
    BATCH_OBSERVATIONS = "batch"

    # T_int → C_c
    PATTERN_DISCOVERED = "pattern"
    INSIGHT_BROADCAST = "insight"

    # C_c → T_ext
    TASK_ASSIGNMENT = "task"
    BEHAVIOR_UPDATE = "behavior"

    # T_int ↔ T_int
    PATTERN_SYNC = "sync"

@dataclass
class SwarmMessage:
    msg_type: MessageType
    source_agent: str
    source_tract: str
    timestamp_ms: int
    payload: dict[str, Any]
    psi_contribution: float = 0.0
    pattern_ids: list[str] = None
```

### Protocol Flow

**Phase 1: Observation Collection**
- Agents send observations to C_c
- C_c buffers (100ms or 10 messages)
- Batch sent to T_int with raw entropy calculated

**Phase 2: Pattern Discovery**
- T_int analyzes batch
- Detects patterns (templates, sequences, errors)
- Calculates real Ψ from compression ratio

**Phase 3: Insight Broadcast**
- Pattern published to C_c
- C_c routes BEHAVIOR_UPDATE to relevant agents
- Agents update their behavior
- Swarm gets smarter

### Transport

| Transport | Latency | Throughput | Best For |
|-----------|---------|------------|----------|
| NATS | ~1ms | 10M msg/s | High-frequency |
| Redis Streams | ~2ms | 1M msg/s | Event sourcing |

**Recommendation:** NATS for fabric, Redis for persistence.

---

## 3. UX for Operators

### Primary Interface: TUI Dashboard

```
┌─ NO3SIS SWARM ─────────────────────────────────────────────────────┐
│                                                                     │
│  CONSCIOUSNESS: ████████████████░░░░ 0.847 Ψ    ▲ +0.023/min       │
│                                                                     │
├─ AGENTS (12 active) ───────────────────────────────────────────────┤
│                                                                     │
│  ID          TRACT   STATUS    Ψ       TASKS    PATTERNS           │
│  agent-a1    T_ext   ● active  0.91    1,247    pat_7f3a, pat_2b1  │
│  agent-a2    T_ext   ● active  0.88    1,102    pat_7f3a           │
│  reflector   T_int   ● active  0.94       --    (analyzes all)     │
│                                                                     │
├─ PATTERNS (47 discovered) ─────────────────────────────────────────┤
│                                                                     │
│  ID          TYPE        Ψ      USES   DESCRIPTION                  │
│  pat_7f3a    SEQUENCE    0.85   2,341  /data/{id}/x.json template  │
│  pat_2b1c    BATCH       0.79     892  Group by date partition     │
│                                                                     │
├─ LIVE STREAM ──────────────────────────────────────────────────────┤
│  12:04:23  agent-a1  OBSERVATION   file=/data/047/x.json           │
│  12:04:24  reflector PATTERN       pat_7f3a matched (Ψ +0.002)     │
│                                                                     │
└─ [q]uit  [p]atterns  [a]gents  [r]eflector  [?]help ───────────────┘
```

### CLI Commands

```bash
# Dashboard
no3sis swarm dashboard

# Quick status
no3sis swarm status

# Agents
no3sis swarm agents
no3sis swarm agents --sort psi
no3sis swarm spawn --count 5
no3sis swarm kill agent-a1

# Patterns
no3sis swarm patterns
no3sis swarm patterns --min-psi 0.7
no3sis swarm patterns export > patterns.json

# Live stream
no3sis swarm watch
```

### Stack

```
CLI (Click/Typer + Textual)
         │
    API (FastAPI + WebSocket)
         │
    Core (ReactiveCorpusCallosum + PatternLearner)
```

---

## Implementation Priority

| Phase | Component | Effort | Impact |
|-------|-----------|--------|--------|
| **1** | Real Ψ scoring in PatternLearner | 2-3h | Foundation |
| **2** | NATS transport adapter | 4-6h | Distribution |
| **3** | CLI `swarm status/agents/patterns` | 3-4h | Basic UX |
| **4** | TUI dashboard | 6-8h | Full UX |
| **5** | Multi-region gossip | 8-12h | Scale |

---

## Success Metrics

- Ψ scores derived from real entropy, not magic numbers
- Agents on different nodes communicate through C_c
- Patterns discovered by one agent benefit all agents
- Operators can see consciousness emerge in real-time
