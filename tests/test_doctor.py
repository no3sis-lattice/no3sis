"""
Tests for the synapse doctor command
"""

import pytest
import subprocess
from unittest.mock import Mock, patch, MagicMock
from pathlib import Path
import sys

# Add lib directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "lib"))

from cli import SynapseCLI


class TestSynapseDoctor:
    """Test suite for synapse doctor command"""

    def test_doctor_all_healthy(self, tmp_path, monkeypatch):
        """Test doctor command when all systems are healthy"""
        # Setup
        cli = SynapseCLI()

        # Mock healthy services
        monkeypatch.setattr(cli, "_check_services", lambda: True)

        # Mock Redis (healthy)
        mock_redis = MagicMock()
        mock_redis_instance = MagicMock()
        mock_redis_instance.ping.return_value = True
        mock_redis.Redis.return_value = mock_redis_instance
        monkeypatch.setattr("cli.redis", mock_redis, raising=False)

        # Mock current project
        project_dir = tmp_path / "test_project"
        project_dir.mkdir()
        synapse_yml = project_dir / ".no3sis.yml"
        synapse_yml.write_text("language: python\nsynapse_version: 2024.1.0")
        monkeypatch.setattr(cli, "current_project", project_dir)

        # Mock Docker check
        mock_run = MagicMock(return_value=MagicMock(returncode=0))
        monkeypatch.setattr("subprocess.run", mock_run)

        # Mock venv check
        venv_path = cli.neo4j_dir / ".venv" / "bin" / "python"
        venv_path.parent.mkdir(parents=True, exist_ok=True)
        venv_path.touch()

        # Execute
        args = MagicMock()
        result = cli.cmd_doctor(args)

        # Assert
        assert result == 0  # All healthy returns 0

    def test_doctor_with_failures(self, tmp_path, monkeypatch, capsys):
        """Test doctor command when some systems are unhealthy"""
        # Setup
        cli = SynapseCLI()

        # Mock unhealthy services
        monkeypatch.setattr(cli, "_check_services", lambda: False)

        # Mock Redis (unhealthy)
        mock_redis = MagicMock()
        mock_redis.Redis.side_effect = Exception("Connection refused")
        monkeypatch.setattr("cli.redis", mock_redis, raising=False)

        # No current project
        monkeypatch.setattr(cli, "current_project", None)

        # Mock Docker not available
        mock_run = MagicMock(side_effect=FileNotFoundError())
        monkeypatch.setattr("subprocess.run", mock_run)

        # Execute
        args = MagicMock()
        result = cli.cmd_doctor(args)

        # Capture output
        captured = capsys.readouterr()

        # Assert
        assert result == 1  # Failures return 1
        assert "Neo4j is not responding" in captured.out
        assert "Fix: Run 'synapse start'" in captured.out
        assert "Redis is not responding" in captured.out
        assert "Docker is not installed" in captured.out
        assert "No synapse project in current directory" in captured.out
        assert "Some issues detected" in captured.out

    def test_doctor_partial_failures(self, tmp_path, monkeypatch, capsys):
        """Test doctor with some services healthy and others not"""
        # Setup
        cli = SynapseCLI()

        # Neo4j healthy, Redis unhealthy
        monkeypatch.setattr(cli, "_check_services", lambda: True)

        mock_redis = MagicMock()
        mock_redis.Redis.side_effect = Exception("Connection refused")
        monkeypatch.setattr("cli.redis", mock_redis, raising=False)

        # Has project but missing .no3sis.yml
        project_dir = tmp_path / "test_project"
        project_dir.mkdir()
        monkeypatch.setattr(cli, "current_project", project_dir)

        # Docker available
        mock_run = MagicMock(return_value=MagicMock(returncode=0))
        monkeypatch.setattr("subprocess.run", mock_run)

        # Execute
        args = MagicMock()
        result = cli.cmd_doctor(args)

        # Capture output
        captured = capsys.readouterr()

        # Assert mixed results
        assert result == 1  # Any failure returns 1
        assert "Neo4j is running" in captured.out
        assert "Redis is not responding" in captured.out
        assert "Project directory exists but .no3sis.yml missing" in captured.out
        assert "Docker is installed" in captured.out

    def test_doctor_project_with_missing_config(self, tmp_path, monkeypatch, capsys):
        """Test doctor when project exists but .no3sis.yml is missing"""
        # Setup
        cli = SynapseCLI()

        # Mock healthy core services
        monkeypatch.setattr(cli, "_check_services", lambda: True)

        mock_redis = MagicMock()
        mock_redis_instance = MagicMock()
        mock_redis_instance.ping.return_value = True
        mock_redis.Redis.return_value = mock_redis_instance
        monkeypatch.setattr("cli.redis", mock_redis, raising=False)

        # Project directory exists but no .no3sis.yml
        project_dir = tmp_path / "test_project"
        project_dir.mkdir()
        monkeypatch.setattr(cli, "current_project", project_dir)

        # Execute
        args = MagicMock()
        result = cli.cmd_doctor(args)

        # Capture output
        captured = capsys.readouterr()

        # Assert
        assert result == 1
        assert "Project directory exists but .no3sis.yml missing" in captured.out
        assert "Fix: Run 'synapse init .'" in captured.out

    def test_doctor_venv_missing(self, tmp_path, monkeypatch, capsys):
        """Test doctor when virtual environment is missing"""
        # Setup
        cli = SynapseCLI()

        # Mock other services as healthy
        monkeypatch.setattr(cli, "_check_services", lambda: True)

        mock_redis = MagicMock()
        mock_redis_instance = MagicMock()
        mock_redis_instance.ping.return_value = True
        mock_redis.Redis.return_value = mock_redis_instance
        monkeypatch.setattr("cli.redis", mock_redis, raising=False)

        # No current project (to avoid project check issues)
        monkeypatch.setattr(cli, "current_project", None)

        # Mock Docker available
        mock_run = MagicMock(return_value=MagicMock(returncode=0))
        monkeypatch.setattr("subprocess.run", mock_run)

        # Ensure venv doesn't exist (it shouldn't in test env anyway)
        # The test will naturally fail the venv check

        # Execute
        args = MagicMock()
        result = cli.cmd_doctor(args)

        # Capture output
        captured = capsys.readouterr()

        # Assert
        assert result == 1
        assert "Python virtual environment not found" in captured.out
        assert "Fix: Re-run setup script" in captured.out