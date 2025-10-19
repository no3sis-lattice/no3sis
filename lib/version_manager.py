#!/usr/bin/env python3
"""
Synapse System - Version Manager (.py)
======================================

Manages version tracking, checksums, and manifests for synapse agents and system.
"""

import json
import hashlib
from pathlib import Path
from datetime import datetime
from typing import Dict, Any


class VersionManager:
    """Manages versioning for synapse system and agents"""

    def __init__(self, synapse_home: Path):
        self.no3sis_home = synapse_home
        self.agents_dir = synapse_home / ".no3sis" / "agents"
        self.manifest_file = synapse_home / ".no3sis" / "AGENTS_MANIFEST.json"
        self.version_file = synapse_home / ".no3sis" / "VERSION"

    def calculate_file_checksum(self, file_path: Path) -> str:
        """Calculate MD5 checksum of a file"""
        if not file_path.exists():
            return ""

        content = file_path.read_text(encoding='utf-8')
        return hashlib.md5(content.encode()).hexdigest()

    def get_agent_metadata(self, agent_file: Path) -> Dict[str, Any]:
        """Extract metadata from an agent file"""
        if not agent_file.exists():
            return {}

        content = agent_file.read_text()
        stat = agent_file.stat()

        # Extract basic info from markdown header if present
        lines = content.split('\n')
        description = ""
        tools = []

        for line in lines[:20]:  # Check first 20 lines for metadata
            if line.startswith('description:'):
                description = line.split(':', 1)[1].strip()
            elif line.startswith('tools:'):
                tools_str = line.split(':', 1)[1].strip()
                tools = [t.strip() for t in tools_str.split(',')]
            elif description and not line.strip():
                break

        return {
            "name": agent_file.stem,
            "description": description,
            "tools": tools,
            "size_bytes": stat.st_size,
            "modified_time": datetime.fromtimestamp(stat.st_mtime).isoformat(),
            "checksum": self.calculate_file_checksum(agent_file),
            "version": self._generate_agent_version(agent_file)
        }

    def _generate_agent_version(self, agent_file: Path) -> str:
        """Generate version string for agent based on modification time and content"""
        stat = agent_file.stat()
        checksum = self.calculate_file_checksum(agent_file)

        # Use timestamp + short checksum as version
        timestamp = int(stat.st_mtime)
        short_checksum = checksum[:8]
        return f"{timestamp}.{short_checksum}"

    def scan_all_agents(self) -> Dict[str, Dict[str, Any]]:
        """Scan all agent files and return metadata"""
        agents_metadata = {}

        if not self.agents_dir.exists():
            print(f"Warning: Agents directory not found: {self.agents_dir}")
            return agents_metadata

        for agent_file in self.agents_dir.glob("*.md"):
            agent_name = agent_file.stem
            metadata = self.get_agent_metadata(agent_file)
            if metadata:
                agents_metadata[agent_name] = metadata

        return agents_metadata

    def update_manifest(self) -> None:
        """Update the agents manifest file with current agent information"""
        print("🔍 Scanning agents for version information...")

        agents_metadata = self.scan_all_agents()
        system_version = self.get_system_version()

        manifest = {
            "manifest_version": "1.0",
            "generated_at": datetime.now().isoformat(),
            "synapse_version": system_version,
            "agent_count": len(agents_metadata),
            "agents": agents_metadata
        }

        try:
            with open(self.manifest_file, 'w') as f:
                json.dump(manifest, f, indent=2)

            print(f"✅ Updated manifest with {len(agents_metadata)} agents")
            print(f"📄 Manifest saved to: {self.manifest_file}")

        except Exception as e:
            print(f"❌ Failed to update manifest: {e}")
            raise

    def get_system_version(self) -> str:
        """Get the current system version"""
        if self.version_file.exists():
            return self.version_file.read_text().strip()
        return "unknown"

    def load_manifest(self) -> Dict[str, Any]:
        """Load the current agents manifest"""
        if not self.manifest_file.exists():
            return {}

        try:
            with open(self.manifest_file, 'r') as f:
                return json.load(f)
        except Exception as e:
            print(f"Warning: Failed to load manifest: {e}")
            return {}

    def verify_agent_integrity(self, agent_name: str) -> bool:
        """Verify an agent file hasn't been corrupted"""
        manifest = self.load_manifest()
        agents = manifest.get("agents", {})

        if agent_name not in agents:
            print(f"⚠️  Agent {agent_name} not found in manifest")
            return False

        agent_file = self.agents_dir / f"{agent_name}.md"
        if not agent_file.exists():
            print(f"❌ Agent file missing: {agent_file}")
            return False

        expected_checksum = agents[agent_name].get("checksum", "")
        actual_checksum = self.calculate_file_checksum(agent_file)

        if expected_checksum != actual_checksum:
            print(f"❌ Checksum mismatch for {agent_name}")
            print(f"   Expected: {expected_checksum}")
            print(f"   Actual:   {actual_checksum}")
            return False

        print(f"✅ Agent {agent_name} integrity verified")
        return True

    def verify_all_agents(self) -> bool:
        """Verify integrity of all agents"""
        manifest = self.load_manifest()
        agents = manifest.get("agents", {})

        if not agents:
            print("⚠️  No agents found in manifest")
            return False

        all_valid = True
        for agent_name in agents.keys():
            if not self.verify_agent_integrity(agent_name):
                all_valid = False

        if all_valid:
            print("✅ All agents passed integrity checks")
        else:
            print("❌ Some agents failed integrity checks")

        return all_valid

    def get_agent_info(self, agent_name: str) -> Dict[str, Any]:
        """Get detailed information about a specific agent"""
        manifest = self.load_manifest()
        agents = manifest.get("agents", {})

        if agent_name not in agents:
            return {"error": f"Agent {agent_name} not found"}

        agent_info = agents[agent_name].copy()

        # Add live file information
        agent_file = self.agents_dir / f"{agent_name}.md"
        if agent_file.exists():
            current_checksum = self.calculate_file_checksum(agent_file)
            agent_info["current_checksum"] = current_checksum
            agent_info["integrity_ok"] = current_checksum == agent_info.get("checksum", "")
        else:
            agent_info["file_exists"] = False
            agent_info["integrity_ok"] = False

        return agent_info

    def list_agents_summary(self) -> None:
        """Print a summary of all agents"""
        manifest = self.load_manifest()
        agents = manifest.get("agents", {})

        if not agents:
            print("No agents found in manifest")
            return

        print(f"\n📦 Synapse Agents Summary ({len(agents)} total)")
        print("=" * 60)

        for name, info in sorted(agents.items()):
            tools_count = len(info.get("tools", []))
            size_kb = info.get("size_bytes", 0) / 1024
            version = info.get("version", "unknown")

            print(f"• {name:<25} v{version:<15} {tools_count:2d} tools  {size_kb:5.1f}KB")

        print(f"\nManifest generated: {manifest.get('generated_at', 'unknown')}")
        print(f"System version: {manifest.get('synapse_version', 'unknown')}")


def main():
    """CLI interface for version management"""
    import argparse

    parser = argparse.ArgumentParser(description="Synapse Version Manager")
    parser.add_argument("command", choices=["update", "verify", "info", "list"])
    parser.add_argument("agent", nargs="?", help="Agent name (for info command)")

    args = parser.parse_args()

    synapse_home = Path(__file__).parent.parent.resolve()
    vm = VersionManager(synapse_home)

    if args.command == "update":
        vm.update_manifest()
    elif args.command == "verify":
        if args.agent:
            vm.verify_agent_integrity(args.agent)
        else:
            vm.verify_all_agents()
    elif args.command == "info":
        if not args.agent:
            print("Agent name required for info command")
            return 1
        info = vm.get_agent_info(args.agent)
        print(json.dumps(info, indent=2))
    elif args.command == "list":
        vm.list_agents_summary()

    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())