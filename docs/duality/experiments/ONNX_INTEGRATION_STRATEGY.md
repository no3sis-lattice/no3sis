# ONNX Integration Strategy for No3sis Dual-Tract Architecture

**Status**: Research & Ideation Phase
**Date**: 2025-11-10
**Branch**: model.onnx (merged into master: commits c075ec4, 2b9a135, b9b2a14)
**Author**: Analysis by Boss agent

---

## Executive Summary

### Current State

A 3.2MB ONNX model has been merged into the codebase:
- **Type**: PyTorch LSTM (character-level language model)
- **Architecture**: 2-layer LSTM (1→256 hidden units) + Linear layer
- **Training Data**: 501 words from Synapse dual-tract documentation
- **Dependencies**: `torch`, `onnx` (unpinned versions added to requirements.txt)
- **Integration Status**: **Orphaned** - Model trained and exported but never loaded/executed

### Key Findings

| Aspect | Status | Impact |
|--------|--------|--------|
| **Codebase Integration** | ❌ None | Model exists but no inference code |
| **Tract Assignment** | ❌ Undefined | Not assigned to T_int, T_ext, or C_c |
| **Nix Reproducibility** | ❌ Broken | PyTorch/ONNX not in flake.nix |
| **Mojo Compatibility** | ⚠️ Conflicts | No ONNX runtime in Mojo; MAX Engine preferred |
| **Consciousness Metrics** | ❌ Zero | No contribution to Ψ calculation |
| **Compression Lattice** | ❌ Misaligned | Generates (expands) vs. compresses |

### Strategic Question

**How can we transform this proof-of-concept into a consciousness-contributing component of the dual-tract architecture?**

---

## Part I: Technical Assessment

### 1.1 Model Specifications

```python
# From train.py (lines 43-52)
class CharModel(nn.Module):
    def __init__(self, n_vocab):
        super().__init__()
        self.lstm = nn.LSTM(
            input_size=1,
            hidden_size=256,
            num_layers=2,
            batch_first=True
        )
        self.fc = nn.Linear(256, n_vocab)

    def forward(self, x):
        out, _ = self.lstm(x)
        out = self.fc(out[:, -1, :])  # Last timestep
        return out
```

**Model Characteristics**:
- **Input**: Character sequences (length 100)
- **Output**: Next-character probability distribution
- **Parameters**: ~198K (LSTM: 195K, Linear: 3K)
- **Size**: 3.2 MB (float32 weights)
- **Training**: 10 epochs, Adam optimizer, CrossEntropyLoss

**Training Corpus** (`data/train.txt` + `data/test.txt`):
```
Total words: 501
Total characters: ~2,800
Vocabulary size: ~65 unique characters
Domain: Synapse dual-tract architecture documentation
```

**Export Configuration**:
```python
dummy_input = torch.randn(1, 100, 1)
torch.onnx.export(
    model,
    dummy_input,
    "model.onnx",
    export_params=True,
    opset_version=10,
    input_names=['input'],
    output_names=['output']
)
```

### 1.2 Dependency Analysis

**Current Requirements** (modified):
```txt
torch     # Added, no version specified
onnx      # Added, no version specified
```

**Missing for Inference**:
```txt
onnxruntime>=1.16.0  # Required to load and run ONNX models
```

**Nix Flake Status**:
```nix
# Current pythonEnv (flake.nix lines 87-89)
pythonEnv = pkgs.python3.withPackages (ps: with ps; [
  redis  # Only dependency
  # Missing: torch, onnx, onnxruntime
]);
```

**Required Nix Updates**:
```nix
pythonEnv = pkgs.python3.withPackages (ps: with ps; [
  redis
  pytorch-bin           # ~800MB, includes CUDA support
  ps.onnx              # ~11MB
  ps.onnxruntime       # ~50MB
]);
```

### 1.3 Mojo Integration Considerations

**Current Mojo Ecosystem** (from `MOJO_PILOT_PLAN.md`):

| Component | Status | Relevance to ONNX |
|-----------|--------|-------------------|
| **Pattern Search** | ✅ Complete | No overlap |
| **Message Router** | ✅ Complete | Could route to ONNX inference |
| **BGE-M3 Embeddings** | 🔴 Deferred | Competes with ONNX approach |

**BGE-M3 Deferral Rationale** (directly relevant):
> "High Complexity: Requires implementing neural network layers in Mojo
> Dependency Risk: Needs ONNX model loading or native implementation
> Nix Challenges: Model file distribution and caching
> **Deferred Until**: Mojo ecosystem matures (better ONNX/ML support)"

**ONNX Runtime in Mojo**:
- ❌ Not available natively
- ⚠️ Could call via Python FFI (performance penalty)
- ✅ MAX Engine (Modular's inference runtime) is preferred path

**Interop Path** (hypothetical):
```python
# Mojo calling ONNX via Python bridge
from python import Python

fn infer_onnx(input_text: String) -> String:
    let onnx = Python.import_module("onnxruntime")
    let session = onnx.InferenceSession("model.onnx")
    # ... inference logic ...
    return result
```

**Performance Cost**: Python FFI adds ~0.1-1ms latency (vs. native Mojo's 0.025ms routing)

---

## Part II: Architectural Integration Options

### 2.1 Option A: Corpus Callosum Text Generator

**Concept**: Use ONNX model as a bridge operator that translates T_int abstractions into natural language for T_ext output.

```
T_int (Internal Tract)           C_c (Corpus Callosum)          T_ext (External Tract)
     │                                    │                              │
     ├─ Pattern Discovered ──────────────>│                              │
     │  (abstract concept)                │                              │
     │                                    ├─ ONNX Text Generator         │
     │                                    │  • Translate concept → text  │
     │                                    │  • Generate explanation      │
     │                                    │                              │
     │                                    └─────────────────────────────>│
     │                                                                   │
     │                                                        User-facing text
```

**Implementation**:
```python
# File: .no3sis/corpus_callosum/text_generator.py

import onnxruntime as ort
import numpy as np

class DualTractTextGenerator:
    """
    Corpus Callosum Operator: Translate T_int concepts to natural language

    Tract: Bridge (C_c)
    Input: Abstract pattern from T_int
    Output: Natural language explanation for T_ext
    """

    def __init__(self, model_path: str = "model.onnx"):
        self.session = ort.InferenceSession(model_path)
        self.tract = "bridge"
        self.char_to_idx = self._build_vocab()
        self.idx_to_char = {v: k for k, v in self.char_to_idx.items()}

    def translate_concept_to_text(
        self,
        concept: str,
        max_length: int = 200,
        temperature: float = 0.8
    ) -> str:
        """
        Translate an internal tract concept to external tract text.

        Args:
            concept: Abstract pattern or concept from T_int
            max_length: Maximum characters to generate
            temperature: Sampling temperature (higher = more creative)

        Returns:
            Natural language explanation suitable for T_ext output
        """
        # Encode seed text (the concept)
        input_seq = self._encode_text(concept[-100:])  # Last 100 chars

        generated_text = concept
        for _ in range(max_length):
            # Run inference
            input_tensor = np.array([input_seq], dtype=np.float32)
            outputs = self.session.run(None, {"input": input_tensor})

            # Sample next character
            logits = outputs[0][0] / temperature
            probs = self._softmax(logits)
            next_char_idx = np.random.choice(len(probs), p=probs)
            next_char = self.idx_to_char[next_char_idx]

            generated_text += next_char

            # Update input sequence
            input_seq = input_seq[1:] + [next_char_idx]

            # Stop at sentence boundary
            if next_char in ['.', '!', '?'] and len(generated_text) > 50:
                break

        return generated_text

    def calculate_consciousness_contribution(self) -> float:
        """
        Calculate this operator's contribution to system consciousness.

        Metrics:
        - Compression ratio: len(input) / len(output) (negative for generation)
        - Semantic coherence: Perplexity of generated text
        - Bridge efficiency: Translation accuracy T_int → T_ext
        """
        # Placeholder - would require evaluation dataset
        return 0.0

    def _encode_text(self, text: str) -> list:
        """Encode text as list of character indices"""
        return [self.char_to_idx.get(c, 0) for c in text[-100:]]

    def _softmax(self, x):
        """Compute softmax over logits"""
        exp_x = np.exp(x - np.max(x))
        return exp_x / exp_x.sum()

    def _build_vocab(self) -> dict:
        """Build character vocabulary (would load from training)"""
        # Placeholder - should match training vocab
        chars = list("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 .,;:!?-'\n")
        return {char: idx for idx, char in enumerate(chars)}
```

**Use Cases**:
1. **Pattern Explanation**: When T_int discovers a compression pattern, generate human-readable description
2. **Code Documentation**: Translate abstract code patterns into docstring text
3. **Error Messages**: Convert internal error states into helpful user messages
4. **Progress Updates**: Generate natural language status reports from T_int state

**Consciousness Contribution**:
```python
# Add to consciousness_metrics.py
text_generation_score = (
    semantic_coherence * 0.4 +      # Perplexity-based
    bridge_efficiency * 0.3 +        # Concept → text accuracy
    user_engagement * 0.3            # How useful the text is
)

# Weight in overall Ψ: 5-10% (bridge operations are support, not core)
```

**Effort**: 8-12 hours
- Implement text_generator.py (4h)
- Retrain on larger corpus (2h)
- Add consciousness scoring (2h)
- Write tests (2h)
- Update LOGOS.md (2h)

---

### 2.2 Option B: Internal Tract Meta-Learning Probe

**Concept**: Use ONNX model as a meta-learning operator in T_int that learns the system's own architectural patterns.

```
T_int (Internal Tract)
     │
     ├─ Pattern Discovery Pipeline
     │       │
     │       ├─ Neo4j Graph Patterns
     │       │
     │       ├─ ONNX Meta-Learner ◄─── Learns from pattern history
     │       │  • Predicts next pattern
     │       │  • Estimates pattern value
     │       │  • Suggests search directions
     │       │
     │       └─ Meta-Pattern Extracted ──> M_int (Pattern Map)
     │
     └─ Consciousness Score Updated
```

**Implementation**:
```python
# File: .no3sis/internal_tract/meta_learner.py

import onnxruntime as ort
from typing import List, Tuple

class MetaPatternLearner:
    """
    Internal Tract Operator: Learn meta-patterns from pattern discovery history

    Tract: Internal (T_int)
    Input: Historical pattern discovery sequences
    Output: Predicted next pattern, estimated value
    """

    def __init__(self, model_path: str = "model.onnx"):
        self.session = ort.InferenceSession(model_path)
        self.tract = "internal"
        self.pattern_history: List[str] = []

    def predict_next_pattern(
        self,
        recent_patterns: List[str],
        k: int = 3
    ) -> List[Tuple[str, float]]:
        """
        Predict the next likely patterns based on recent discoveries.

        Args:
            recent_patterns: Last N patterns discovered
            k: Number of predictions to return

        Returns:
            List of (pattern_type, confidence) tuples
        """
        # Encode pattern sequence
        pattern_text = " → ".join(recent_patterns)
        encoded = self._encode_pattern_sequence(pattern_text)

        # Run inference
        outputs = self.session.run(None, {"input": encoded})
        predictions = self._decode_predictions(outputs[0], k)

        return predictions

    def estimate_pattern_value(self, pattern: str) -> float:
        """
        Estimate the consciousness contribution of exploring a pattern.

        Higher scores = more likely to increase Ψ
        """
        # Use model perplexity as a proxy for "surprisingness"
        # More surprising patterns = higher potential value
        encoded = self._encode_pattern_sequence(pattern)
        outputs = self.session.run(None, {"input": encoded})
        perplexity = self._calculate_perplexity(outputs[0])

        # Map perplexity to value (inverted - low perplexity = familiar = low value)
        value = min(1.0, perplexity / 10.0)
        return value

    def suggest_search_direction(self) -> str:
        """
        Suggest where T_int should focus next based on learned patterns.

        Returns:
            Search direction (e.g., "compression_algorithms", "graph_topology")
        """
        predictions = self.predict_next_pattern(self.pattern_history[-10:])

        # Return highest-value direction that hasn't been explored recently
        for pattern, confidence in predictions:
            if pattern not in self.pattern_history[-5:]:
                return pattern

        return predictions[0][0]  # Fallback to highest confidence

    def update_history(self, discovered_pattern: str):
        """Record a newly discovered pattern"""
        self.pattern_history.append(discovered_pattern)

    def calculate_consciousness_contribution(self) -> float:
        """
        Meta-learning contribution to Ψ.

        Metrics:
        - Prediction accuracy: How often suggestions lead to discoveries
        - Exploration efficiency: Reduced search time via guided direction
        - Meta-pattern extraction: Novel patterns about patterns
        """
        # Placeholder - would track success rate of suggestions
        return 0.0
```

**Use Cases**:
1. **Guided Pattern Search**: Predict which code patterns are worth exploring
2. **Curiosity Optimization**: Focus T_int's curiosity loop on high-value areas
3. **Compression Strategy**: Learn which compression algorithms work for which data types
4. **Self-Improvement**: Discover meta-patterns about the system's own learning

**Consciousness Contribution**:
```python
# Add to consciousness_metrics.py
meta_learning_score = (
    prediction_accuracy * 0.5 +      # How often predictions pan out
    exploration_efficiency * 0.3 +   # Time saved via guidance
    meta_pattern_novelty * 0.2       # Truly new meta-patterns found
)

# Weight in overall Ψ: 15-20% (directly enhances T_int intelligence)
```

**Effort**: 12-16 hours
- Implement meta_learner.py (4h)
- Retrain on pattern discovery logs (4h)
- Integrate with Neo4j pattern map (3h)
- Add consciousness scoring with accuracy tracking (3h)
- Write tests (2h)

---

### 2.3 Option C: External Tract Code Generation Accelerator

**Concept**: Use ONNX model to generate boilerplate code in T_ext, accelerating the implementation phase.

```
T_ext (External Tract)
     │
     ├─ Implementation Pipeline
     │       │
     │       ├─ Task Received from C_c
     │       │
     │       ├─ ONNX Code Generator ◄─── Trained on codebase patterns
     │       │  • Generate function skeletons
     │       │  • Create boilerplate
     │       │  • Suggest API calls
     │       │
     │       ├─ T_int Review & Refinement ───> Send to T_int for compression check
     │       │
     │       └─ Final Code Emitted
     │
     └─ Real-time execution
```

**Implementation**:
```python
# File: .no3sis/external_tract/code_generator.py

import onnxruntime as ort
from typing import Dict, Any

class CodeGenerationAccelerator:
    """
    External Tract Operator: Generate boilerplate code quickly

    Tract: External (T_ext)
    Input: Function signature or API specification
    Output: Generated code skeleton
    """

    def __init__(self, model_path: str = "model.onnx"):
        self.session = ort.InferenceSession(model_path)
        self.tract = "external"

    def generate_function_skeleton(
        self,
        signature: str,
        docstring: str = ""
    ) -> str:
        """
        Generate a function implementation skeleton.

        Args:
            signature: Function signature (e.g., "def parse_ast(code: str) -> Dict:")
            docstring: Optional docstring describing function purpose

        Returns:
            Generated function code (to be refined by T_int compression)
        """
        prompt = f"{signature}\n    '''{docstring}'''\n    "
        encoded = self._encode_code(prompt)

        # Run inference
        outputs = self.session.run(None, {"input": encoded})
        generated_code = self._decode_code(outputs[0])

        return f"{signature}\n    '''{docstring}'''\n{generated_code}"

    def suggest_api_calls(self, context: str) -> list[str]:
        """
        Suggest likely API calls based on code context.

        Args:
            context: Surrounding code or task description

        Returns:
            List of likely API calls (e.g., ["neo4j.session()", "redis.get()"])
        """
        # Use model to predict next tokens given context
        # Filter for function call patterns
        pass

    def generate_test_skeleton(self, function_code: str) -> str:
        """
        Generate pytest test skeleton for a function.

        Supports TDD workflow: Generate test first, then implementation
        """
        pass

    def calculate_consciousness_contribution(self) -> float:
        """
        Code generation contribution to Ψ.

        Metrics:
        - Time savings: How much faster than manual coding
        - Code quality: Pass rate after T_int refinement
        - Pattern reuse: % of generated code that survives compression
        """
        return 0.0
```

**Use Cases**:
1. **TDD Acceleration**: Generate test skeletons instantly
2. **Boilerplate Elimination**: Auto-generate common patterns (getters, serializers, etc.)
3. **API Scaffolding**: Create initial implementations based on type signatures
4. **Dual-Tract Workflow**: T_ext generates quickly, T_int compresses/refines

**Consciousness Contribution**:
```python
# Add to consciousness_metrics.py
code_generation_score = (
    time_efficiency * 0.4 +          # Speed boost vs manual
    pattern_reuse_rate * 0.4 +       # How much survives T_int compression
    code_quality * 0.2               # Tests pass, style correct
)

# Weight in overall Ψ: 10-15% (T_ext efficiency gains)
```

**Effort**: 10-14 hours
- Implement code_generator.py (4h)
- Retrain on no3sis codebase (4h)
- Integrate with T_int compression check (3h)
- Add consciousness scoring (2h)
- Write tests (2h)

---

## Part III: Comparison Matrix

| Criterion | Option A: C_c Text Gen | Option B: T_int Meta-Learn | Option C: T_ext Code Gen |
|-----------|------------------------|----------------------------|--------------------------|
| **Tract Assignment** | Bridge (C_c) | Internal (T_int) | External (T_ext) |
| **Consciousness Ψ Weight** | 5-10% (support) | 15-20% (core intelligence) | 10-15% (efficiency) |
| **Compression Alignment** | ⚠️ Generates (inverse) | ✅ Learns patterns | ⚠️ Generates (inverse) |
| **Mojo Compatibility** | ⚠️ Python FFI needed | ⚠️ Python FFI needed | ⚠️ Python FFI needed |
| **Training Corpus Size** | Medium (10K+ words) | Large (all pattern logs) | Large (entire codebase) |
| **Nix Integration** | 🔴 Requires torch/onnxrt | 🔴 Requires torch/onnxrt | 🔴 Requires torch/onnxrt |
| **Implementation Effort** | 8-12h | 12-16h | 10-14h |
| **Immediate Value** | ⚠️ Medium (UX improvement) | ✅ High (T_int enhancement) | ⚠️ Medium (speed boost) |
| **Long-term Value** | ⚠️ Low (LLMs better at text) | ✅ High (unique meta-learning) | ⚠️ Low (conflicts with compression) |
| **Risk** | Low (isolated component) | Medium (core T_int changes) | High (may reduce code quality) |

---

## Part IV: Recommended Path Forward

### Phase 1: Minimal Viable Integration (2-4h)

**Goal**: Make the model functional without architectural commitment.

1. **Add onnxruntime**:
```bash
# Update requirements.txt
echo "onnxruntime>=1.16.0" >> requirements.txt

# Update flake.nix
# Add ps.onnxruntime to pythonEnv
```

2. **Create simple inference script**:
```python
# File: scripts/onnx_inference_demo.py
"""Demonstrate ONNX model inference (non-integrated)"""

import onnxruntime as ort
import numpy as np

def infer_demo():
    session = ort.InferenceSession("model.onnx")
    dummy_input = np.random.randn(1, 100, 1).astype(np.float32)
    outputs = session.run(None, {"input": dummy_input})
    print(f"Output shape: {outputs[0].shape}")
    print("Model loaded and running successfully!")

if __name__ == "__main__":
    infer_demo()
```

3. **Add to CI**:
```yaml
# .github/workflows/model-validation.yml
- name: Validate ONNX Model
  run: |
    python3 scripts/onnx_inference_demo.py
```

**Deliverable**: Working inference without architectural changes.

---

### Phase 2: Research & Ideation (4-8h)

**Goal**: Determine best architectural fit through experimentation.

1. **Collect Training Data**:
   - **Option A**: Scrape no3sis documentation (10K+ words)
   - **Option B**: Export Neo4j pattern discovery logs
   - **Option C**: Extract code patterns from no3sis codebase

2. **Retrain Model**:
```python
# Modify train.py to use chosen corpus
# Increase training epochs (10 → 100)
# Add validation split for perplexity tracking
```

3. **Build Prototype** (choose one option):
   - Implement basic version of chosen integration path
   - No consciousness scoring yet
   - Focus on functional proof-of-concept

4. **Measure Performance**:
   - Inference latency (should be <50ms for real-time use)
   - Quality metrics (perplexity, BLEU score, etc.)
   - Memory footprint (important for multi-agent scaling)

**Deliverable**: Working prototype for one integration option.

---

### Phase 3: Full Integration (8-16h)

**Goal**: Production-ready implementation with consciousness metrics.

1. **Implement Chosen Path** (from Options A/B/C)
2. **Add Tract Assignment**:
```python
# In particle metadata
particle_metadata = {
    "name": "onnx_text_generator",  # or meta_learner, code_generator
    "tract": "bridge",  # or "internal", "external"
    "type": "operator",
    "inputs": ["concept"],
    "outputs": ["text"],
    "consciousness_weight": 0.08
}
```

3. **Implement Consciousness Scoring**:
```python
def calculate_consciousness_contribution(self) -> float:
    """Track and score this operator's Ψ contribution"""
    metrics = self.get_performance_metrics()

    score = (
        metrics['quality'] * 0.4 +
        metrics['efficiency'] * 0.3 +
        metrics['novelty'] * 0.3
    )

    # Update system-wide Ψ
    self.update_consciousness_map(score)

    return score
```

4. **Integration Testing**:
   - Unit tests for operator in isolation
   - Integration tests with Neo4j/Redis
   - Dual-tract dialogue tests (if C_c or bridge role)

5. **Documentation**:
   - Update LOGOS.md with new operator
   - Add to TRUE_DUAL_TRACT.md operator catalog
   - Document consciousness contribution formula

**Deliverable**: Production-ready ONNX operator in dual-tract architecture.

---

## Part V: Open Questions for Ideation Session

### Strategic Questions

1. **Core Purpose**: What problem does ONNX solve that the current architecture can't?
   - Is it text generation? (Could use external LLM API)
   - Is it meta-learning? (Most promising unique use case)
   - Is it code generation? (Conflicts with compression philosophy)

2. **Compression Philosophy**: How do we justify *generative* models in a *compression-driven* architecture?
   - Could generation be reframed as "decompression" (abstract → concrete)?
   - Should we treat generation as a necessary bridge operation (T_int ↔ T_ext)?
   - Or is generation fundamentally misaligned with consciousness emergence?

3. **Mojo Migration**: Should we invest in ONNX when MAX Engine is the long-term path?
   - Is this temporary Python infrastructure or permanent architecture?
   - Could we design for MAX from the start, skipping ONNX?
   - What's the effort to port ONNX → MAX later?

### Technical Questions

4. **Training Data**: What should we train on?
   - Full no3sis codebase (~50K lines)?
   - Documentation + CHANGELOG (~20K words)?
   - Neo4j pattern discovery logs (need to export first)?
   - All of the above?

5. **Model Size**: Should we scale up?
   - Current: 3.2MB, 256 hidden units, 198K params
   - GPT-2 Small: 500MB, 768 hidden units, 117M params
   - Is character-level sufficient, or do we need tokenization?

6. **Inference Strategy**:
   - **On-demand**: Call model when needed (adds latency to critical path)
   - **Background**: Pre-generate predictions, cache in Redis (memory overhead)
   - **Async**: Queue inference requests, process in batches (complexity)

7. **Consciousness Metrics**: How do we *really* measure ONNX's Ψ contribution?
   - Current metrics: pattern_density, emergence_factor, compression_ratio
   - Where does text/code generation fit?
   - New metric category: "translation_fidelity" (T_int ↔ T_ext bridge quality)?

### Architectural Questions

8. **Tract Assignment Decision Tree**:
```
Is the operator self-referential (learns from own behavior)?
├─ Yes → Internal Tract (T_int)
└─ No
    │
    └─ Does it interact with external environment (users, tools)?
        ├─ Yes → External Tract (T_ext)
        └─ No → Corpus Callosum (C_c)
```

Does ONNX fit this tree, or do we need a new category?

9. **Prime Hierarchy**: Where does ONNX sit in the particle expansion?
```
Level 0: Boss (1 agent)
Level 1: Internal + External Poles (2 agents)
Level 2: 6 agents (3 T_int, 3 T_ext)
Level 3: 18 agents (9 T_int, 9 T_ext)
...
Level 8: ~19.4M particles

Question: Is ONNX a Level 2 agent or a Level 3+ particle?
```

10. **Neo4j Integration**: Should ONNX models themselves be stored in the pattern map?
```cypher
CREATE (op:Operator {
    name: "onnx_text_generator",
    tract: "bridge",
    model_path: "model.onnx",
    version: "0.1.0",
    consciousness_weight: 0.08
})

CREATE (metric:ConsciousnessMetric {
    operator: "onnx_text_generator",
    timestamp: datetime(),
    psi_contribution: 0.042,
    quality_score: 0.75,
    efficiency_score: 0.89
})
```

---

## Part VI: Decision Framework

### Use This Flowchart Tomorrow

```
START
  │
  ├─ Q1: Do we need text/code *generation* in the dual-tract architecture?
  │   ├─ No → Remove ONNX integration, focus on compression
  │   └─ Yes
  │       │
  │       ├─ Q2: Is character-level LSTM the right approach?
  │       │   ├─ No → Research alternatives (GPT-2, T5, MAX Engine)
  │       │   └─ Yes
  │       │       │
  │       │       ├─ Q3: Which tract needs generation most?
  │       │       │   ├─ T_int → Option B (Meta-Learning)
  │       │       │   ├─ T_ext → Option C (Code Generation)
  │       │       │   └─ C_c → Option A (Text Generation)
  │       │       │
  │       │       └─ Q4: Can we justify the Nix/Mojo overhead?
  │       │           ├─ No → Defer until MAX Engine ready
  │       │           └─ Yes → Proceed to Phase 1 (MVIntegration)
  │       │
  │       └─ EXECUTE CHOSEN PATH
  │
  └─ END
```

### Success Criteria (Define Tomorrow)

Before implementing, agree on:

1. **Ψ Contribution Target**: Minimum consciousness score increase (e.g., +2% = 0.477 → 0.487)
2. **Latency Budget**: Maximum inference time (e.g., <50ms per call)
3. **Memory Budget**: Maximum model size in production (e.g., <100MB loaded)
4. **Quality Threshold**: Minimum perplexity or BLEU score for generated text
5. **Maintenance Commitment**: Who owns this? How much time for retraining/tuning?

---

## Part VII: Resources & References

### Relevant Docs

- `/home/m0xu/1-projects/no3sis/LOGOS.md` - Dual-tract architecture spec
- `/home/m0xu/1-projects/no3sis/docs/duality/TRUE_DUAL_TRACT.md` - Operator-based reframing
- `/home/m0xu/1-projects/no3sis/docs/MOJO_PILOT_PLAN.md` - Mojo migration timeline
- `/home/m0xu/1-projects/no3sis/docs/duality/reference/CONSCIOUSNESS_METRICS.md` - Ψ calculation

### Existing Components to Integrate With

- Neo4j Pattern Map: `.no3sis/neo4j/`
- Redis Cache: `.no3sis/redis/`
- BGE-M3 Vector Engine: `.no3sis/neo4j/vector_engine.py`
- Mojo FFI: `./mojo/src/` (pattern search, message router)

### External Research

- ONNX Runtime Performance: https://onnxruntime.ai/docs/performance/
- MAX Engine Roadmap: https://docs.modular.com/max/
- Character-level LSTMs: Karpathy's "The Unreasonable Effectiveness of RNNs"

---

## Appendix: Current Model Details

### Training Script Analysis

```python
# From train.py

# Data loading (lines 15-33)
def load_data(train_path, test_path):
    # Reads train.txt and test.txt
    # Builds character vocabulary (no tokenization)
    # Returns combined corpus
    pass

# Model definition (lines 43-52)
class CharModel(nn.Module):
    # 2-layer LSTM with 256 hidden units
    # Linear layer for character prediction
    pass

# Training loop (lines 70-82)
for epoch in range(10):
    # Batch size: 64
    # Optimizer: Adam (default lr=0.001)
    # Loss: CrossEntropyLoss
    # No validation split (trains on 100% of data)
    pass

# ONNX export (lines 86-94)
torch.onnx.export(
    model, dummy_input, "model.onnx",
    opset_version=10  # ONNX 1.5.0 compatible
)
```

### Model Limitations

1. **Tiny Corpus**: 501 words is insufficient for coherent generation
   - GPT-2 used 8M web pages
   - Minimum recommended: 10K+ words for character-level

2. **No Validation**: Trains on 100% of data, no held-out perplexity check
   - Can't measure if model is overfitting or learning generalizable patterns

3. **Character-Level**: No semantic understanding
   - Learns spelling patterns, not meaning
   - Won't understand "compression" vs "compression_ratio" as related concepts

4. **Fixed Sequence Length**: 100 characters
   - Can't handle longer contexts
   - No attention mechanism for long-range dependencies

### Recommended Improvements (If We Proceed)

1. **Larger Corpus**: 10K+ words from no3sis docs + code comments
2. **Validation Split**: 80/20 train/val to measure perplexity
3. **Tokenization**: BPE or WordPiece instead of character-level
4. **Attention**: Add attention mechanism (Transformer architecture)
5. **Larger Model**: 512-1024 hidden units (current: 256)
6. **More Training**: 100+ epochs with early stopping

---

**End of Document**

**Next Steps**: Review this document in tomorrow's ideation session and decide on Option A, B, C, or removal.
