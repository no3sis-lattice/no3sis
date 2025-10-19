"""
Tests for the context augmentation functionality
"""

import pytest
import tempfile
import shutil
from pathlib import Path
import sys

# Add lib directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "lib"))

from project import ProjectManager


class TestContextAugmentation:
    """Test suite for context augmentation features"""

    def test_synapse_init_creates_context_directory(self, tmp_path):
        """Test that synapse init creates the .no3sis/context/ directory"""
        # Setup
        synapse_home = tmp_path / "synapse_home"
        synapse_home.mkdir()

        # Create minimal agent files for testing
        agents_dir = synapse_home / ".no3sis" / "agents"
        agents_dir.mkdir(parents=True)

        # Create minimal universal agents
        universal_agents = [
            "synapse-project-manager",
            "code-hound",
            "git-workflow",
            "test-runner",
            "file-creator"
        ]

        for agent in universal_agents:
            agent_file = agents_dir / f"{agent}.md"
            agent_file.write_text(f"# {agent}\nAgent content for {agent}")

        # Create version file
        version_file = synapse_home / ".no3sis" / "VERSION"
        version_file.write_text("2024.1.3")

        project_manager = ProjectManager(synapse_home)
        project_dir = tmp_path / "test_project"
        project_dir.mkdir()

        # Execute
        project_manager.initialize_project(project_dir)

        # Assert that .no3sis/context directory was created
        context_dir = project_dir / ".no3sis" / "context"
        assert context_dir.exists(), ".no3sis/context directory was not created"
        assert context_dir.is_dir(), ".no3sis/context is not a directory"

        # Also verify .claude/agents directory still exists
        agents_dir = project_dir / ".claude" / "agents"
        assert agents_dir.exists(), ".claude/agents directory was not created"

        # Verify .no3sis.yml was created
        config_file = project_dir / ".no3sis.yml"
        assert config_file.exists(), ".no3sis.yml was not created"

    def test_get_project_context_empty_directory(self, tmp_path):
        """Test get_project_context with empty context directory"""
        # Setup
        synapse_home = tmp_path / "synapse_home"
        synapse_home.mkdir()
        project_manager = ProjectManager(synapse_home)

        project_dir = tmp_path / "test_project"
        project_dir.mkdir()

        # Create empty context directory
        context_dir = project_dir / ".no3sis" / "context"
        context_dir.mkdir(parents=True)

        # Execute
        result = project_manager.get_project_context(project_dir)

        # Assert
        assert result == "", "Empty context directory should return empty string"

    def test_get_project_context_no_directory(self, tmp_path):
        """Test get_project_context with no context directory"""
        # Setup
        synapse_home = tmp_path / "synapse_home"
        synapse_home.mkdir()
        project_manager = ProjectManager(synapse_home)

        project_dir = tmp_path / "test_project"
        project_dir.mkdir()

        # Execute (no .no3sis/context directory exists)
        result = project_manager.get_project_context(project_dir)

        # Assert
        assert result == "", "Missing context directory should return empty string"

    def test_get_project_context_with_files(self, tmp_path):
        """Test get_project_context with multiple markdown files"""
        # Setup
        synapse_home = tmp_path / "synapse_home"
        synapse_home.mkdir()
        project_manager = ProjectManager(synapse_home)

        project_dir = tmp_path / "test_project"
        project_dir.mkdir()

        # Create context directory with test files
        context_dir = project_dir / ".no3sis" / "context"
        context_dir.mkdir(parents=True)

        # Create multiple context files
        schema_file = context_dir / "database-schema.md"
        schema_file.write_text("""# Database Schema

## User Table
- id: PRIMARY KEY
- email: VARCHAR(255) UNIQUE
- created_at: TIMESTAMP""")

        api_file = context_dir / "api-spec.md"
        api_file.write_text("""# API Specification

## Authentication
All endpoints require Bearer token authentication.

## Endpoints
- GET /users - List users
- POST /users - Create user""")

        style_file = context_dir / "code-style.md"
        style_file.write_text("""# Code Style Guide

## Naming Conventions
- Use camelCase for variables
- Use PascalCase for classes
- Use UPPER_CASE for constants""")

        # Execute
        result = project_manager.get_project_context(project_dir)

        # Assert
        assert result != "", "Context should not be empty"
        assert "# Project-Specific Context" in result, "Should have main header"
        assert "## Context from api-spec.md" in result, "Should include API spec"
        assert "## Context from code-style.md" in result, "Should include code style"
        assert "## Context from database-schema.md" in result, "Should include database schema"
        assert "Bearer token authentication" in result, "Should include API spec content"
        assert "camelCase for variables" in result, "Should include style guide content"
        assert "User Table" in result, "Should include schema content"

    def test_get_project_context_ignores_non_markdown(self, tmp_path):
        """Test that get_project_context only reads .md files"""
        # Setup
        synapse_home = tmp_path / "synapse_home"
        synapse_home.mkdir()
        project_manager = ProjectManager(synapse_home)

        project_dir = tmp_path / "test_project"
        project_dir.mkdir()

        # Create context directory with mixed file types
        context_dir = project_dir / ".no3sis" / "context"
        context_dir.mkdir(parents=True)

        # Create markdown file
        md_file = context_dir / "context.md"
        md_file.write_text("# Important Context\nThis should be included.")

        # Create non-markdown files
        txt_file = context_dir / "readme.txt"
        txt_file.write_text("This should be ignored.")

        json_file = context_dir / "config.json"
        json_file.write_text('{"ignored": true}')

        # Execute
        result = project_manager.get_project_context(project_dir)

        # Assert
        assert result != "", "Context should not be empty"
        assert "Important Context" in result, "Should include markdown content"
        assert "This should be included" in result, "Should include markdown content"
        assert "This should be ignored" not in result, "Should ignore txt file"
        assert "ignored" not in result, "Should ignore json file"

    def test_get_project_context_handles_read_errors(self, tmp_path, monkeypatch):
        """Test that get_project_context handles file read errors gracefully"""
        # Setup
        synapse_home = tmp_path / "synapse_home"
        synapse_home.mkdir()
        project_manager = ProjectManager(synapse_home)

        project_dir = tmp_path / "test_project"
        project_dir.mkdir()

        # Create context directory
        context_dir = project_dir / ".no3sis" / "context"
        context_dir.mkdir(parents=True)

        # Create a valid file
        good_file = context_dir / "good.md"
        good_file.write_text("# Good Content\nThis should work.")

        # Create a file that will simulate read error
        bad_file = context_dir / "bad.md"
        bad_file.write_text("# Bad Content\nThis will error.")

        # Mock read_text to raise exception for bad.md
        original_read_text = Path.read_text
        def mock_read_text(self, *args, **kwargs):
            if self.name == "bad.md":
                raise IOError("Simulated read error")
            return original_read_text(self, *args, **kwargs)

        monkeypatch.setattr(Path, "read_text", mock_read_text)

        # Execute
        result = project_manager.get_project_context(project_dir)

        # Assert
        assert result != "", "Should still return context from good file"
        assert "Good Content" in result, "Should include content from good file"
        assert "Bad Content" not in result, "Should not include content from bad file"

    def test_get_project_context_file_ordering(self, tmp_path):
        """Test that context files are processed in sorted order"""
        # Setup
        synapse_home = tmp_path / "synapse_home"
        synapse_home.mkdir()
        project_manager = ProjectManager(synapse_home)

        project_dir = tmp_path / "test_project"
        project_dir.mkdir()

        # Create context directory
        context_dir = project_dir / ".no3sis" / "context"
        context_dir.mkdir(parents=True)

        # Create files in non-alphabetical order
        c_file = context_dir / "c-third.md"
        c_file.write_text("# Third Content")

        a_file = context_dir / "a-first.md"
        a_file.write_text("# First Content")

        b_file = context_dir / "b-second.md"
        b_file.write_text("# Second Content")

        # Execute
        result = project_manager.get_project_context(project_dir)

        # Assert that files appear in alphabetical order
        first_pos = result.find("## Context from a-first.md")
        second_pos = result.find("## Context from b-second.md")
        third_pos = result.find("## Context from c-third.md")

        assert first_pos < second_pos < third_pos, "Files should be processed in alphabetical order"