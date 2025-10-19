# Git Workflow Agent 🌿

**Specialized git workflow automation with Synapse System integration for intelligent branch management, commit operations, and PR creation.**

## Overview

Git Workflow Agent has been successfully migrated from a static Markdown specification to a fully functional Python agent with executable tools, Synapse integration, and inter-agent coordination. This migration implements intelligent git operations following Agent OS conventions.

## Agent Architecture

```
git-workflow/
├── git_workflow_agent.py        # Main executable agent
├── git_workflow_config.yml      # Configuration with Sonnet model settings
├── git_workflow_prompt.md       # Agent identity and behavioral instructions
├── README.md                    # This documentation
└── tools/
    ├── __init__.py              # Tool package definition
    ├── git_operations.py        # Core git commands with safety checks
    ├── workflow_automation.py   # Complete workflow execution
    ├── pr_management.py         # Pull request creation and management
    ├── synapse_integration.py   # Knowledge base connectivity
    ├── agent_communication.py   # Inter-agent coordination
    ├── config_manager.py        # Configuration management
    └── mock_sdk.py              # Development fallback
```

## Key Capabilities

### 🌿 Intelligent Branch Management
- **Agent OS Conventions**: Extract branch names from spec folders, remove date prefixes
- **Safety Checks**: Verify uncommitted changes before switching
- **Smart Naming**: Kebab-case conversion and validation
- **Branch Analysis**: Health checks and recommendations

### 💾 Smart Commit Operations
- **Conventional Commits**: Automatic type detection and formatting
- **Message Enhancement**: Synapse-powered message improvement
- **Quality Analysis**: Commit message scoring and recommendations
- **Intelligent Staging**: Pattern-based file selection

### 🚀 Complete Workflow Automation
- **Feature Workflow**: Branch creation → Commit → Push → PR
- **Hotfix Workflow**: Urgent fixes with priority labels and notifications
- **Release Workflow**: Version tagging and release management
- **Agent Coordination**: Multi-agent workflow orchestration

### 📝 Enhanced PR Management
- **Template-Driven**: Synapse-powered PR descriptions
- **Auto-Linking**: Connect to specs, issues, and related work
- **Label Management**: Automatic label assignment based on workflow type
- **Review Coordination**: Request reviews from relevant agents

### 🔍 Repository Intelligence
- **Status Analysis**: Comprehensive repository health checking
- **Pattern Recognition**: Identify workflow optimization opportunities
- **Metric Tracking**: Monitor workflow performance and efficiency
- **Recommendation Engine**: Suggest improvements based on analysis

## Configuration

Git Workflow uses **Claude-3-Sonnet** as the primary model for standard git operations with cost optimization:

- **High/Medium Complexity**: Sonnet (workflow automation, merge resolution)
- **Low Complexity**: Haiku (status checks, simple commands)
- **Cost-Effective**: Prefers cheaper models when appropriate

### Agent OS Git Conventions
```yaml
commit_format: "conventional"        # feat:, fix:, docs:, etc.
branch_naming: "kebab-case"         # feature-name, not feature_name
remove_date_prefixes: true         # 2025-01-29-feature → feature
require_pr: true                   # Always create PRs for features
```

## Usage Examples

### Complete Feature Workflow
```python
from git_workflow_agent import execute_complete_workflow

result = await execute_complete_workflow({
    "action": "feature",
    "spec_folder": ".agent-os/specs/2025-01-29-user-authentication",
    "target_branch": "main",
    "pr_title": "Add user authentication system"
})

print(f"✅ Workflow complete: {result['pr_url']}")
```

### Smart Branch Management
```python
from git_workflow_agent import manage_git_branches

# Create feature branch from spec folder
result = await manage_git_branches({
    "action": "create",
    "branch_name": "user-authentication",  # Extracted from spec folder
    "source_branch": "main"
})

print(f"✅ Created branch: {result['branch_name']}")
```

### Intelligent Commit Creation
```python
from git_workflow_agent import smart_commit

result = await smart_commit({
    "message": "implement user authentication",  # Will be enhanced to "feat: implement user authentication"
    "files": None,  # Stage all changes
    "amend": False
})

print(f"✅ Commit: {result['commit_hash']}")
print(f"📊 Quality score: {result['message_analysis']['quality_score']}/100")
```

### Repository Status Analysis
```python
from git_workflow_agent import check_repository_status

status = await check_repository_status()

print(f"📊 Branch: {status['current_branch']}")
print(f"📊 Uncommitted: {status['uncommitted_changes']} files")
print("💡 Recommendations:")
for rec in status['recommendations']:
    print(f"  - {rec}")
```

## Agent OS Integration

### Spec Folder Processing
```bash
# Input spec folder:
.agent-os/specs/2025-01-29-user-authentication/

# Generated branch name:
user-authentication

# Generated commit:
feat: implement user authentication

# Generated PR title:
Add User Authentication
```

### Conventional Commits
```bash
# Input messages are enhanced:
"add login feature"           → "feat: add login feature"
"fix authentication bug"      → "fix: authentication bug"
"update documentation"        → "docs: update documentation"
```

### Safety Protocols
- ✅ **Never force push** without explicit permission
- ✅ **Check uncommitted changes** before branch switching
- ✅ **Verify remote exists** before pushing
- ✅ **Confirm destructive operations** like branch deletion

## Workflow Types

### 1. Feature Development
```yaml
Steps:
  1. Extract branch name from spec folder
  2. Create/switch to feature branch
  3. Stage and commit changes with conventional format
  4. Push branch with upstream tracking
  5. Create PR with enhanced template
  6. Coordinate with agents for review
```

### 2. Hotfix Process
```yaml
Steps:
  1. Start from main/production branch
  2. Create hotfix branch with urgent prefix
  3. Commit fix with appropriate message
  4. Push with urgent labels
  5. Create priority PR with stakeholder notifications
  6. Coordinate expedited review process
```

### 3. Release Management
```yaml
Steps:
  1. Ensure clean working directory
  2. Determine next semantic version
  3. Create annotated release tag
  4. Push tag to remote repository
  5. Generate release notes (optional)
  6. Notify stakeholders of release
```

## Synapse Integration

### Standards Retrieval
- **Commit Conventions**: Fetch organizational commit message standards
- **Branch Rules**: Get branch naming conventions and requirements
- **PR Templates**: Retrieve pull request templates and checklists
- **Workflow Patterns**: Access proven workflow methodologies

### Pattern Learning
- **Successful Workflows**: Learn from historical workflow data
- **Optimization Opportunities**: Identify process improvements
- **Convention Evolution**: Track changes in organizational standards
- **Metric Analysis**: Monitor workflow efficiency trends

### Knowledge Sharing
- **Workflow Metrics**: Publish performance data to knowledge graph
- **Pattern Discovery**: Share successful workflow innovations
- **Best Practices**: Contribute to organizational learning
- **Standard Updates**: Propose improvements based on usage data

## Agent Coordination

### Project Manager Integration
```python
# Coordinates with synapse-project-manager
coordination = await coordinate_workflow_with_agents("feature", {
    "spec_folder": ".agent-os/specs/feature-name",
    "target_branch": "main"
})

print(f"🤝 Coordinated with: {coordination['agents_contacted']}")
```

### Code Quality Integration
```python
# Notifies code-hound for pre-PR quality checks
review_request = await request_code_review(
    pr_url="https://github.com/org/repo/pull/123",
    reviewers=["code-hound", "python-specialist"]
)
```

## Testing

The agent includes comprehensive testing capabilities:

```bash
# Test git operations
python -c "from tools.git_operations import check_git_status; ..."

# Test workflow automation
python -c "from tools.workflow_automation import execute_git_workflow; ..."

# Test configuration
python -c "from tools.config_manager import load_config; ..."
```

## Migration Success Metrics

✅ **Fully Migrated**: From static Markdown to executable Python agent
✅ **Tool Integration**: 7 specialized tool modules with 25+ functions
✅ **Workflow Automation**: Complete feature/hotfix/release workflows
✅ **Safety Protocols**: Comprehensive checks preventing destructive operations
✅ **Synapse Integration**: Knowledge base connectivity for standards and patterns
✅ **Agent Coordination**: Multi-agent workflow orchestration
✅ **Convention Compliance**: Agent OS git standards implementation
✅ **Model Optimization**: Cost-effective Sonnet/Haiku routing

## Phase 3 Impact

Git Workflow's migration completes the **Phase 3 Orchestration Layer** with:

1. **Intelligent Automation**: End-to-end git workflow execution
2. **Safety-First Operations**: Comprehensive checks preventing data loss
3. **Convention Enforcement**: Automatic compliance with Agent OS standards
4. **Multi-Agent Coordination**: Seamless integration with project management
5. **Knowledge Integration**: Synapse-powered standards and pattern recognition

The agent is now ready for production use and provides immediate value through automated, safe, and intelligent git operations that follow organizational conventions.

---

*"Efficient git operations with clean history and project conventions"* 🌿