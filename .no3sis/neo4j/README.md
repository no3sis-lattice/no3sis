# Synapse Core Scripts

This directory contains the core scripts that power the Synapse System's knowledge retrieval and management capabilities.

## Primary Agent Tools

### `synapse_search.py`
**Purpose:** Intelligent context retrieval from the hybrid Neo4j/Redis system
**Usage:** `python synapse_search.py "query" [max_results]`
**Tool:** SynapseSearch - Used by all 16 agents
**Returns:** JSON with search results and metadata

### `synapse_standard.py` 
**Purpose:** Retrieve language-specific coding standards
**Usage:** `python synapse_standard.py <standard_name> <language>`
**Tool:** SynapseStandard - Get naming conventions, testing strategies, etc.
**Example:** `python synapse_standard.py naming-conventions rust`

### `synapse_template.py` 
**Purpose:** Access project templates with variable substitution
**Usage:** `python synapse_template.py <template_name> [variables_json]`
**Tool:** SynapseTemplate - Mission docs, specs, API docs, etc.
**Example:** `python synapse_template.py mission '{"PROJECT_NAME": "MyApp"}'`

### `synapse_health.py` 
**Purpose:** Comprehensive system health check
**Usage:** `python synapse_health.py`
**Tool:** SynapseHealth - Check Neo4j, Redis, Python env, scripts
**Returns:** Status + recommendations for fixing issues

## Core Components

### `context_manager.py`
**Purpose:** Central API for intelligent context retrieval
**Features:** Redis caching, Neo4j graph traversal, result synthesis
**Used by:** synapse_search.py

### `vector_engine.py`
**Purpose:** BGE-M3 embedding engine for semantic search
**Features:** 1024-dimensional vectors, similarity search
**Used by:** context_manager.py

### `ingestion.py`
**Purpose:** Knowledge base ingestion and updates
**Features:** File processing, graph creation, vector embedding
**Usage:** Manual execution for knowledge base updates

### `activate.sh`
**Purpose:** Activates the Python virtual environment
**Usage:** Source this script before running Python tools

## Integration with Claude Code

All scripts integrate with Claude Code agents via:
- **tool-mapping.json:** Maps agent tools to actual scripts
- **synapse_tools.py:** Python wrapper for programmatic access
- **16 specialized agents:** Each has access to all Synapse tools

## Workflow

1. **Setup:** `activate.sh` → Python environment ready
2. **Ingestion:** `ingestion.py` → Knowledge loaded into Neo4j
3. **Embeddings:** `vector_engine.py` → Semantic vectors generated
4. **Agent Usage:** Agents call SynapseSearch/Standard/Template/Health tools
5. **Results:** JSON responses with data + usage guidance

## System Status
- In progress
