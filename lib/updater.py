#!/usr/bin/env python3
"""
Synapse System - Update Manager
===============================

Handles version checking and updating of project agents and configurations.
"""

import os
import shutil
import hashlib
from pathlib import Path
from typing import Dict, List, Optional, Any
from datetime import datetime

from project import ProjectManager


class UpdateManager:
    """Manages updates for synapse projects"""

    def __init__(self, synapse_home: Path):
        self.no3sis_home = synapse_home
        self.project_manager = ProjectManager(synapse_home)
        self.agents_source = synapse_home / ".no3sis" / "agents"

    def check_updates(self, project_dir: Path) -> List[Dict[str, Any]]:
        """Check for available updates to project agents and configuration"""
        updates = []

        # Load project configuration
        config = self.project_manager.load_project_config(project_dir)
        if not config:
            raise Exception("Project configuration not found")

        # Get current system versions
        current_system_version = self.project_manager.get_system_version()
        current_agent_versions = self.project_manager.get_agent_versions()

        # Check system version update
        project_version = config.get("synapse_version", "unknown")
        if project_version != current_system_version:
            updates.append({
                "type": "system",
                "name": "synapse-system",
                "old_version": project_version,
                "new_version": current_system_version,
                "description": "Core system update"
            })

        # Check agent updates
        project_agent_versions = config.get("agent_versions", {})
        deployment_method = config.get("deployment_method", "copy")

        for agent_name, old_version in project_agent_versions.items():
            current_version = current_agent_versions.get(agent_name)

            if not current_version:
                # Agent no longer exists in system
                updates.append({
                    "type": "agent_removed",
                    "name": agent_name,
                    "old_version": old_version,
                    "new_version": None,
                    "description": f"Agent {agent_name} removed from system"
                })
                continue

            # For symlinked agents, updates are automatic
            if deployment_method == "symlink":
                agent_file = project_dir / ".claude" / "agents" / f"{agent_name}.md"
                if agent_file.is_symlink():
                    continue  # Symlinked agents auto-update

            # Check if update is needed
            if old_version != current_version:
                updates.append({
                    "type": "agent",
                    "name": agent_name,
                    "old_version": old_version,
                    "new_version": current_version,
                    "description": f"Updated {agent_name} agent"
                })

        # Check for new universal agents
        current_universal = set(self.project_manager.get_universal_agents())
        project_agents = set(project_agent_versions.keys())
        missing_universal = current_universal - project_agents

        for agent_name in missing_universal:
            if agent_name in current_agent_versions:
                updates.append({
                    "type": "agent_new",
                    "name": agent_name,
                    "old_version": None,
                    "new_version": current_agent_versions[agent_name],
                    "description": f"New universal agent: {agent_name}"
                })

        return updates

    def apply_updates(self, project_dir: Path, updates: List[Dict[str, Any]]) -> None:
        """Apply updates to a project"""
        config = self.project_manager.load_project_config(project_dir)
        if not config:
            raise Exception("Project configuration not found")

        deployment_method = config.get("deployment_method", "copy")
        use_links = deployment_method == "symlink"

        # Create backup of current configuration
        backup_config = config.copy()

        # Apply each update
        for update in updates:
            update_type = update["type"]
            name = update["name"]

            if update_type == "system":
                # Update system version
                config["synapse_version"] = update["new_version"]
                print(f"✓ Updated system version to {update['new_version']}")

            elif update_type == "agent":
                # Update agent file
                success = self.project_manager.copy_or_link_agent(
                    name, project_dir, use_links
                )
                if success:
                    config["agent_versions"][name] = update["new_version"]
                    print(f"✓ Updated {name} agent")
                else:
                    print(f"⚠️  Failed to update {name} agent")

            elif update_type == "agent_new":
                # Add new agent
                success = self.project_manager.copy_or_link_agent(
                    name, project_dir, use_links
                )
                if success:
                    if "agent_versions" not in config:
                        config["agent_versions"] = {}
                    config["agent_versions"][name] = update["new_version"]
                    print(f"✓ Added new {name} agent")
                else:
                    print(f"⚠️  Failed to add {name} agent")

            elif update_type == "agent_removed":
                # Remove obsolete agent
                agent_file = project_dir / ".claude" / "agents" / f"{name}.md"
                if agent_file.exists():
                    try:
                        agent_file.unlink()
                        del config["agent_versions"][name]
                        print(f"✓ Removed obsolete {name} agent")
                    except Exception as e:
                        print(f"⚠️  Failed to remove {name} agent: {e}")

        # Update timestamp
        config["updated_at"] = datetime.now().isoformat()

        # Save updated configuration
        try:
            self.project_manager.save_project_config(project_dir, config)
        except Exception as e:
            # Restore backup on failure
            self.project_manager.save_project_config(project_dir, backup_config)
            raise Exception(f"Failed to save updated configuration: {e}")

    def check_all_projects(self, base_path: Path = None) -> Dict[str, List[Dict[str, Any]]]:
        """Check for updates across all synapse projects in a directory tree"""
        if base_path is None:
            base_path = Path.home()

        project_updates = {}

        def scan_directory(directory: Path):
            try:
                for item in directory.iterdir():
                    if item.is_dir():
                        # Check if this is a synapse project
                        if (item / ".no3sis.yml").exists():
                            try:
                                updates = self.check_updates(item)
                                if updates:
                                    project_updates[str(item)] = updates
                            except Exception as e:
                                print(f"⚠️  Error checking {item}: {e}")

                        # Recursively scan subdirectories (but skip common non-project dirs)
                        if item.name not in {'.git', 'node_modules', 'target', '__pycache__', '.venv'}:
                            scan_directory(item)
            except PermissionError:
                # Skip directories we can't read
                pass

        scan_directory(base_path)
        return project_updates

    def migrate_legacy_project(self, project_dir: Path) -> bool:
        """Migrate a legacy project to new versioning system"""
        config_file = project_dir / ".no3sis.yml"
        if not config_file.exists():
            return False

        config = self.project_manager.load_project_config(project_dir)
        if not config:
            return False

        # Check if already migrated
        if "synapse_version" in config and "agent_versions" in config:
            return True  # Already migrated

        print(f"🔄 Migrating legacy project: {project_dir.name}")

        # Add missing version tracking
        config["synapse_version"] = self.project_manager.get_system_version()

        # Detect current agents and their versions
        agents_dir = project_dir / ".claude" / "agents"
        if agents_dir.exists():
            agent_versions = {}
            current_system_versions = self.project_manager.get_agent_versions()

            for agent_file in agents_dir.glob("*.md"):
                agent_name = agent_file.stem
                # Use current system version for existing agents
                agent_versions[agent_name] = current_system_versions.get(
                    agent_name, "legacy"
                )

            config["agent_versions"] = agent_versions

        # Add deployment method detection
        sample_agent = agents_dir / "synapse-project-manager.md" if agents_dir.exists() else None
        if sample_agent and sample_agent.exists():
            config["deployment_method"] = "symlink" if sample_agent.is_symlink() else "copy"
        else:
            config["deployment_method"] = "copy"

        # Update timestamp
        config["updated_at"] = datetime.now().isoformat()

        # Save migrated configuration
        try:
            self.project_manager.save_project_config(project_dir, config)
            print("✓ Migration completed")
            return True
        except Exception as e:
            print(f"⚠️  Migration failed: {e}")
            return False

    def rollback_update(self, project_dir: Path, backup_config: Dict[str, Any]) -> bool:
        """Rollback a failed update"""
        try:
            # Restore agents from backup
            if "agent_versions" in backup_config:
                agents_dir = project_dir / ".claude" / "agents"
                deployment_method = backup_config.get("deployment_method", "copy")
                use_links = deployment_method == "symlink"

                # Remove all current agents
                if agents_dir.exists():
                    for agent_file in agents_dir.glob("*.md"):
                        agent_file.unlink()

                # Restore agents from backup versions
                for agent_name in backup_config["agent_versions"]:
                    self.project_manager.copy_or_link_agent(
                        agent_name, project_dir, use_links
                    )

            # Restore configuration
            self.project_manager.save_project_config(project_dir, backup_config)
            print("✓ Successfully rolled back to previous version")
            return True

        except Exception as e:
            print(f"❌ Rollback failed: {e}")
            return False

    def get_update_summary(self, updates: List[Dict[str, Any]]) -> str:
        """Generate a human-readable summary of updates"""
        if not updates:
            return "No updates available"

        summary_lines = []
        system_updates = [u for u in updates if u["type"] == "system"]
        agent_updates = [u for u in updates if u["type"] == "agent"]
        new_agents = [u for u in updates if u["type"] == "agent_new"]
        removed_agents = [u for u in updates if u["type"] == "agent_removed"]

        if system_updates:
            summary_lines.append(f"System: {system_updates[0]['old_version']} → {system_updates[0]['new_version']}")

        if agent_updates:
            summary_lines.append(f"Agent updates: {len(agent_updates)}")

        if new_agents:
            summary_lines.append(f"New agents: {len(new_agents)}")

        if removed_agents:
            summary_lines.append(f"Removed agents: {len(removed_agents)}")

        return ", ".join(summary_lines)