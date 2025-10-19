#!/usr/bin/env python3
"""
Synapse System Ingestion Engine
===============================

This script discovers, processes, and ingests files from the no3sis-system
directories into Neo4j knowledge graph and prepares for vector indexing.

The Feighnburm Constant: Acknowledge emergent complexity, map it systematically.
"""

import os
import json
import hashlib
import sqlite3
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from datetime import datetime

import requests
from neo4j import GraphDatabase
import redis
from dotenv import load_dotenv
from vector_engine import VectorEngine

load_dotenv()

class SynapseIngestion:
    def __init__(self):
        self.no3sis_root = Path.home() / ".no3sis-system"
        self.neo4j_uri = os.getenv("NEO4J_URI", "bolt://localhost:7687")
        self.neo4j_user = os.getenv("NEO4J_USER", "neo4j")
        self.neo4j_password = os.getenv("NEO4J_PASSWORD", "no3sis_neo4j_pass")
        self.redis_host = os.getenv("REDIS_HOST", "localhost")
        self.redis_port = int(os.getenv("REDIS_PORT", 6379))
        self.redis_password = os.getenv("REDIS_PASSWORD", None)

        # Initialize connections
        self.driver = None
        self.redis_client = None
        self.sqlite_path = self.no3sis_root / "neo4j" / "vector_store.db"
        self.vector_engine = VectorEngine(self.no3sis_root)

        # File tracking
        self.processed_files = set()
        self.file_hashes = {}

    def connect(self):
        """Initialize connections to Neo4j and Redis"""
        try:
            self.driver = GraphDatabase.driver(
                self.neo4j_uri,
                auth=(self.neo4j_user, self.neo4j_password)
            )
            # Test connection
            with self.driver.session() as session:
                session.run("RETURN 1")
            print("✓ Neo4j connection established")

        except Exception as e:
            print(f"✗ Neo4j connection failed: {e}")
            return False

        try:
            self.redis_client = redis.Redis(
                host=self.redis_host,
                port=self.redis_port,
                password=self.redis_password,
                decode_responses=True
            )
            self.redis_client.ping()
            print("✓ Redis connection established")

        except Exception as e:
            print(f"✗ Redis connection failed: {e}")
            return False

        return True

    def initialize_sqlite(self):
        """Initialize SQLite database for vector storage"""
        self.vector_engine.initialize_vector_store()
        print("✓ Vector storage initialized")

    def discover_files(self) -> List[Path]:
        """Discover all relevant files in no3sis-system directories"""
        target_dirs = ["instructions", "standards", "workflows", "templates"]
        files = []

        for dir_name in target_dirs:
            dir_path = self.no3sis_root / ".no3sis" / dir_name
            if dir_path.exists():
                files.extend(dir_path.rglob("*.md"))
                files.extend(dir_path.rglob("*.sh"))
                files.extend(dir_path.rglob("*.py"))
                files.extend(dir_path.rglob("*.txt"))

        print(f"✓ Discovered {len(files)} files for processing")
        return files

    def calculate_file_hash(self, file_path: Path) -> str:
        """Calculate SHA-256 hash of file content"""
        sha256_hash = hashlib.sha256()
        with open(file_path, "rb") as f:
            for byte_block in iter(lambda: f.read(4096), b""):
                sha256_hash.update(byte_block)
        return sha256_hash.hexdigest()

    def generate_ai_summary(self, content: str, file_path: str) -> str:
        """
        Generate AI summary of file content
        For now, returns a simple rule-based summary.
        This can be enhanced with actual AI API calls later.
        """
        # Simple rule-based summary for now
        lines = content.split('\n')
        non_empty_lines = [line.strip() for line in lines if line.strip()]

        # Extract key information
        summary_parts = []

        # File type identification
        if file_path.endswith('.md'):
            summary_parts.append("Documentation file")
        elif file_path.endswith('.sh'):
            summary_parts.append("Shell script")
        elif file_path.endswith('.py'):
            summary_parts.append("Python script")

        # Look for headers, functions, or key patterns
        for line in non_empty_lines[:10]:  # First 10 lines
            if line.startswith('#'):
                summary_parts.append(f"Contains: {line[:50]}")
                break
            elif 'def ' in line or 'function ' in line:
                summary_parts.append(f"Defines: {line[:50]}")
                break

        # Content length indicator
        word_count = len(content.split())
        summary_parts.append(f"~{word_count} words")

        return " | ".join(summary_parts)

    def process_file(self, file_path: Path) -> Optional[str]:
        """Process a single file and create Neo4j node"""
        try:
            # Read file content
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()

            # Calculate hash
            content_hash = self.calculate_file_hash(file_path)

            # Generate summary
            summary = self.generate_ai_summary(content, str(file_path))

            # Relative path from no3sis root
            rel_path = file_path.relative_to(self.no3sis_root)

            # Create Neo4j node
            with self.driver.session() as session:
                result = session.run("""
                    MERGE (f:SynapseFile {path: $path})
                    SET f.name = $name,
                        f.summary = $summary,
                        f.content = $content,
                        f.hash = $hash,
                        f.size = $size,
                        f.type = $type,
                        f.updated_at = datetime(),
                        f.word_count = $word_count
                    RETURN elementId(f) as node_id
                """,
                path=str(rel_path),
                name=file_path.name,
                summary=summary,
                content=content,
                hash=content_hash,
                size=len(content),
                type=file_path.suffix[1:] if file_path.suffix else 'unknown',
                word_count=len(content.split())
                )

                record = result.single()
                if record:
                    node_id = record["node_id"]

                    # Generate and store vector embedding
                    try:
                        # Use content + summary for richer embeddings
                        embedding_text = f"{summary}\n\n{content}"
                        embedding = self.vector_engine.generate_embedding(embedding_text, str(file_path))
                        self.vector_engine.store_embedding(node_id, str(rel_path), content_hash, embedding)
                        print(f"✓ Processed: {rel_path} (with embedding)")
                    except Exception as e:
                        print(f"⚠ Processed: {rel_path} (embedding failed: {e})")

                    return node_id

        except Exception as e:
            print(f"✗ Error processing {file_path}: {e}")
            return None

    def create_relationships(self):
        """Create relationships between files based on content and structure"""
        with self.driver.session() as session:
            # First, clear existing relationships to avoid duplicates
            session.run("MATCH ()-[r:CONTAINS|REFERENCES|SIMILAR_TO]->() DELETE r")

            # Create directory containment relationships (parent dir contains child file)
            session.run("""
                MATCH (child:SynapseFile)
                WHERE child.path CONTAINS '/'
                WITH child, substring(child.path, 0, size(child.path) - size(split(child.path, '/')[-1]) - 1) as parent_path
                MATCH (parent:SynapseFile {path: parent_path})
                MERGE (parent)-[:CONTAINS]->(child)
            """)

            # Create relationships based on file references (more precise)
            session.run("""
                MATCH (a:SynapseFile), (b:SynapseFile)
                WHERE a.path <> b.path
                AND (
                    a.content CONTAINS b.path
                    OR a.content CONTAINS b.name
                    OR (size(b.name) > 5 AND a.content CONTAINS substring(b.name, 0, size(b.name)-3))
                )
                MERGE (a)-[:REFERENCES]->(b)
            """)

            # Create type-based grouping relationships
            session.run("""
                MATCH (a:SynapseFile), (b:SynapseFile)
                WHERE a.path <> b.path
                AND a.type = b.type
                AND a.type IN ['md', 'py', 'sh']
                AND split(a.path, '/')[0] = split(b.path, '/')[0]
                MERGE (a)-[:SIMILAR_TO]->(b)
            """)

            print("✓ Created structural and semantic relationships")

    def update_ingestion_metadata(self):
        """Update metadata about the ingestion process"""
        metadata = {
            "last_ingestion": datetime.now().isoformat(),
            "files_processed": len(self.processed_files),
            "no3sis_root": str(self.no3sis_root)
        }

        if self.redis_client:
            self.redis_client.setex("no3sis:ingestion_metadata", 3600, json.dumps(metadata))

        # Also store in Neo4j
        with self.driver.session() as session:
            session.run("""
                MERGE (meta:SynapseMetadata {type: 'ingestion'})
                SET meta.last_run = datetime(),
                    meta.files_processed = $files_processed,
                    meta.no3sis_root = $no3sis_root
            """,
            files_processed=len(self.processed_files),
            no3sis_root=str(self.no3sis_root)
            )

    def get_existing_file_hashes(self) -> Dict[str, str]:
        """Get existing file hashes from Neo4j to detect changes"""
        existing_hashes = {}
        try:
            with self.driver.session() as session:
                result = session.run("""
                    MATCH (f:SynapseFile)
                    RETURN f.path as path, f.hash as hash
                """)
                for record in result:
                    existing_hashes[record["path"]] = record["hash"]
        except Exception as e:
            print(f"Warning: Could not retrieve existing hashes: {e}")
        return existing_hashes

    def remove_deleted_files(self, current_files: List[Path]):
        """Remove nodes for files that no longer exist"""
        current_paths = set(str(f.relative_to(self.no3sis_root)) for f in current_files)

        try:
            with self.driver.session() as session:
                # Get all existing file paths
                result = session.run("MATCH (f:SynapseFile) RETURN f.path as path")
                existing_paths = {record["path"] for record in result}

                # Find deleted files
                deleted_paths = existing_paths - current_paths

                if deleted_paths:
                    print(f"🗑️  Removing {len(deleted_paths)} deleted files...")
                    for path in deleted_paths:
                        session.run("""
                            MATCH (f:SynapseFile {path: $path})
                            DETACH DELETE f
                        """, path=path)

                        # Also remove from vector storage
                        conn = sqlite3.connect(self.sqlite_path)
                        cursor = conn.cursor()
                        cursor.execute("DELETE FROM vector_metadata WHERE file_path = ?", (path,))
                        cursor.execute("DELETE FROM vectors WHERE neo4j_node_id IN (SELECT neo4j_node_id FROM vector_metadata WHERE file_path = ?)", (path,))
                        conn.commit()
                        conn.close()

                    print(f"✓ Removed {len(deleted_paths)} deleted files")
        except Exception as e:
            print(f"Warning: Could not clean up deleted files: {e}")

    def run_full_ingestion(self, force_refresh: bool = False):
        """Run the complete ingestion process with incremental updates"""
        print("🧠 Starting Synapse System Ingestion...")

        if not self.connect():
            print("✗ Failed to establish connections")
            return False

        self.initialize_sqlite()

        # Get existing file hashes for change detection
        existing_hashes = {} if force_refresh else self.get_existing_file_hashes()

        if force_refresh:
            print("🔄 Force refresh: clearing all existing data...")
            with self.driver.session() as session:
                session.run("MATCH (n:SynapseFile) DETACH DELETE n")
                session.run("MATCH (n:SynapseMetadata) DELETE n")
            # Clear vector storage
            self.vector_engine.clear_embeddings()

        # Discover and process files
        files = self.discover_files()

        # Remove deleted files (unless force refresh already cleared everything)
        if not force_refresh:
            self.remove_deleted_files(files)

        files_processed = 0
        files_updated = 0
        files_skipped = 0

        for file_path in files:
            rel_path = str(file_path.relative_to(self.no3sis_root))
            current_hash = self.calculate_file_hash(file_path)

            # Check if file has changed
            if rel_path in existing_hashes and existing_hashes[rel_path] == current_hash:
                files_skipped += 1
                continue

            # Process the file
            node_id = self.process_file(file_path)
            if node_id:
                self.processed_files.add(str(file_path))
                if rel_path in existing_hashes:
                    files_updated += 1
                else:
                    files_processed += 1

        # Create relationships
        self.create_relationships()

        # Update metadata
        self.update_ingestion_metadata()

        print(f"✅ Ingestion complete:")
        print(f"   📄 New files processed: {files_processed}")
        print(f"   🔄 Files updated: {files_updated}")
        print(f"   ⏭️  Files skipped (unchanged): {files_skipped}")
        print(f"   📊 Total files in system: {len(self.processed_files) + files_skipped}")

        return True

    def load_pattern_map(self) -> Optional[Dict]:
        """Load pattern map from JSON file"""
        pattern_map_file = self.no3sis_root / ".no3sis" / "particles" / "pattern_map.json"

        if not pattern_map_file.exists():
            print(f"⚠ Pattern map not found at {pattern_map_file}")
            print("  Patterns will be ingested after orchestrator runs discover them")
            return None

        try:
            with open(pattern_map_file, 'r') as f:
                data = json.load(f)
            print(f"✓ Loaded pattern map: {len(data.get('patterns', {}))} patterns")
            return data
        except Exception as e:
            print(f"✗ Failed to load pattern map: {e}")
            return None

    def process_pattern(self, pattern_id: str, pattern_data: Dict) -> Optional[str]:
        """Process a single pattern and create Neo4j node"""
        try:
            # Extract pattern properties
            name = pattern_data.get('name', 'Unknown Pattern')
            description = pattern_data.get('description', '')
            pattern_type = pattern_data.get('pattern_type', 'unknown')
            action_sequence = pattern_data.get('action_sequence', [])
            entropy_reduction = pattern_data.get('entropy_reduction', 0.0)
            consciousness_contribution = pattern_data.get('consciousness_contribution', 'low')
            occurrence_count = pattern_data.get('occurrence_count', 1)
            success_rate = pattern_data.get('success_rate', 1.0)
            discovered_at = pattern_data.get('discovered_at', 0.0)

            # Create searchable text for embedding
            action_seq_str = " → ".join(action_sequence) if action_sequence else "no sequence"
            embedding_text = f"{name}\n{description}\nActions: {action_seq_str}\nType: {pattern_type}"

            # Create Neo4j node
            with self.driver.session() as session:
                result = session.run("""
                    MERGE (p:Pattern {pattern_id: $pattern_id})
                    SET p.name = $name,
                        p.description = $description,
                        p.pattern_type = $pattern_type,
                        p.action_sequence = $action_sequence,
                        p.entropy_reduction = $entropy_reduction,
                        p.consciousness_contribution = $consciousness_contribution,
                        p.occurrence_count = $occurrence_count,
                        p.success_rate = $success_rate,
                        p.discovered_at = $discovered_at,
                        p.updated_at = datetime(),
                        p.searchable_text = $searchable_text
                    RETURN elementId(p) as node_id
                """,
                pattern_id=pattern_id,
                name=name,
                description=description,
                pattern_type=pattern_type,
                action_sequence=action_sequence,
                entropy_reduction=entropy_reduction,
                consciousness_contribution=consciousness_contribution,
                occurrence_count=occurrence_count,
                success_rate=success_rate,
                discovered_at=discovered_at,
                searchable_text=embedding_text
                )

                record = result.single()
                if record:
                    node_id = record["node_id"]

                    # Generate and store vector embedding
                    try:
                        embedding = self.vector_engine.generate_embedding(embedding_text, f"pattern:{pattern_id}")
                        self.vector_engine.store_embedding(node_id, f"pattern:{pattern_id}", pattern_id, embedding)
                        return node_id
                    except Exception as e:
                        print(f"⚠ Pattern {pattern_id[:16]}... processed (embedding failed: {e})")
                        return node_id

        except Exception as e:
            print(f"✗ Error processing pattern {pattern_id[:16]}...: {e}")
            return None

    def run_pattern_ingestion(self, force_refresh: bool = False) -> bool:
        """Ingest patterns from pattern_map.json into Neo4j"""
        print("🧠 Starting Pattern Ingestion...")

        if not self.connect():
            print("✗ Failed to establish connections")
            return False

        self.initialize_sqlite()

        # Load pattern map
        pattern_map = self.load_pattern_map()
        if not pattern_map:
            print("⚠ No patterns to ingest")
            return True  # Not an error, just nothing to do

        patterns = pattern_map.get('patterns', {})
        if not patterns:
            print("⚠ Pattern map is empty")
            return True

        if force_refresh:
            print("🔄 Force refresh: clearing existing patterns...")
            with self.driver.session() as session:
                result = session.run("MATCH (p:Pattern) DETACH DELETE p RETURN count(p) as deleted")
                deleted = result.single()['deleted']
                print(f"   Deleted {deleted} existing patterns")

        # Process patterns
        patterns_processed = 0
        patterns_failed = 0

        for pattern_id, pattern_data in patterns.items():
            node_id = self.process_pattern(pattern_id, pattern_data)
            if node_id:
                patterns_processed += 1
                if patterns_processed % 10 == 0:
                    print(f"   Processed {patterns_processed}/{len(patterns)} patterns...")
            else:
                patterns_failed += 1

        # Update metadata
        with self.driver.session() as session:
            session.run("""
                MERGE (meta:SynapseMetadata {type: 'pattern_ingestion'})
                SET meta.last_run = datetime(),
                    meta.patterns_processed = $patterns_processed,
                    meta.total_patterns = $total_patterns,
                    meta.consciousness_level = $consciousness_level
            """,
            patterns_processed=patterns_processed,
            total_patterns=len(patterns),
            consciousness_level=pattern_map.get('consciousness_level', 0.0)
            )

        print(f"✅ Pattern ingestion complete:")
        print(f"   🧠 Patterns processed: {patterns_processed}")
        print(f"   ✗ Patterns failed: {patterns_failed}")
        print(f"   📊 Consciousness level: {pattern_map.get('consciousness_level', 0.0):.2f}")

        return True

    def close(self):
        """Close connections"""
        if self.driver:
            self.driver.close()
        if self.redis_client:
            self.redis_client.close()

def main():
    """Main entry point"""
    import sys

    force_refresh = "--force" in sys.argv or "-f" in sys.argv
    patterns_only = "--patterns" in sys.argv or "-p" in sys.argv
    include_patterns = patterns_only or "--all" in sys.argv or "-a" in sys.argv

    if "--help" in sys.argv or "-h" in sys.argv:
        print("Synapse System Ingestion Engine")
        print()
        print("Usage: python ingestion.py [OPTIONS]")
        print()
        print("Options:")
        print("  --force, -f      Force full refresh (clear existing data)")
        print("  --patterns, -p   Ingest patterns only (from pattern_map.json)")
        print("  --all, -a        Ingest both files and patterns")
        print("  --help, -h       Show this help message")
        print()
        print("Default: Incremental file ingestion (only process changed files)")
        print("         Use --patterns to ingest discovered patterns into Neo4j")
        return 0

    ingestion = SynapseIngestion()
    try:
        if patterns_only:
            # Only ingest patterns
            success = ingestion.run_pattern_ingestion(force_refresh=force_refresh)
        elif include_patterns:
            # Ingest both files and patterns
            success = ingestion.run_full_ingestion(force_refresh=force_refresh)
            if success:
                print()
                success = ingestion.run_pattern_ingestion(force_refresh=force_refresh)
        else:
            # Default: files only
            success = ingestion.run_full_ingestion(force_refresh=force_refresh)

        return 0 if success else 1
    except KeyboardInterrupt:
        print("\n⚠️  Ingestion interrupted by user")
        return 1
    except Exception as e:
        print(f"✗ Fatal error: {e}")
        return 1
    finally:
        ingestion.close()

if __name__ == "__main__":
    exit(main())