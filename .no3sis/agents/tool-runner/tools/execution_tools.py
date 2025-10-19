"""
Command Execution Tools

Core functionality for safely executing commands and scripts.
"""

import os
import asyncio
import subprocess
import tempfile
import shlex
from pathlib import Path
from typing import Dict, Any, List, Optional, Union
import time
import signal


# Security: Whitelist of allowed commands
ALLOWED_COMMANDS = {
    # Version control
    "git", "svn", "hg",
    # File operations
    "ls", "cat", "head", "tail", "find", "grep", "awk", "sed",
    # Package managers
    "npm", "yarn", "pip", "cargo", "go", "mvn", "gradle",
    # Build tools
    "make", "cmake", "ninja", "docker", "docker-compose",
    # Languages
    "python", "python3", "node", "rustc", "javac", "gcc", "g++",
    # Testing
    "pytest", "jest", "cargo test", "go test", "mvn test",
    # System info
    "ps", "top", "df", "du", "uname", "whoami",
    # Network (safe subset)
    "curl", "wget", "ping"
}

# Commands that require special handling
RESTRICTED_COMMANDS = {
    "rm", "rmdir", "mv", "cp", "chmod", "chown", "sudo", "su",
    "kill", "killall", "pkill", "systemctl", "service"
}


async def execute_command(command: str, timeout: int = 30, working_dir: Optional[str] = None) -> Dict[str, Any]:
    """
    Execute a shell command safely with timeout and validation.

    Args:
        command: Command to execute
        timeout: Timeout in seconds
        working_dir: Working directory for command execution

    Returns:
        Dict with execution results and status
    """
    try:
        # Security validation
        validation_result = _validate_command(command)
        if not validation_result["safe"]:
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Command blocked for security: {validation_result['reason']}"
                }],
                "success": False,
                "exit_code": -1,
                "security_block": True
            }

        # Parse command safely
        try:
            cmd_parts = shlex.split(command)
        except ValueError as e:
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Invalid command syntax: {str(e)}"
                }],
                "success": False,
                "exit_code": -1
            }

        # Set working directory
        cwd = working_dir if working_dir and Path(working_dir).exists() else os.getcwd()

        # Execute command with timeout
        start_time = time.time()

        process = await asyncio.create_subprocess_exec(
            *cmd_parts,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            cwd=cwd
        )

        try:
            stdout, stderr = await asyncio.wait_for(
                process.communicate(),
                timeout=timeout
            )
        except asyncio.TimeoutError:
            process.kill()
            await process.wait()
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Command timed out after {timeout} seconds"
                }],
                "success": False,
                "exit_code": -1,
                "timeout": True
            }

        execution_time = time.time() - start_time
        stdout_text = stdout.decode('utf-8', errors='ignore')
        stderr_text = stderr.decode('utf-8', errors='ignore')

        # Format results
        result_text = f"Command: {command}\n"
        result_text += f"Exit code: {process.returncode}\n"
        result_text += f"Execution time: {execution_time:.2f}s\n\n"

        if stdout_text:
            result_text += f"STDOUT:\n{stdout_text}\n"

        if stderr_text:
            result_text += f"STDERR:\n{stderr_text}\n"

        return {
            "content": [{
                "type": "text",
                "text": result_text
            }],
            "success": process.returncode == 0,
            "exit_code": process.returncode,
            "stdout": stdout_text,
            "stderr": stderr_text,
            "execution_time": execution_time,
            "working_directory": cwd
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Command execution failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def execute_script(script_path: str, args: List[str] = None, timeout: int = 60) -> Dict[str, Any]:
    """
    Execute a script file with arguments.

    Args:
        script_path: Path to script file
        args: List of arguments to pass to script
        timeout: Timeout in seconds

    Returns:
        Dict with execution results and status
    """
    try:
        script_file = Path(script_path)

        if not script_file.exists():
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Script not found: {script_path}"
                }],
                "success": False,
                "error": "script_not_found"
            }

        # Determine script interpreter
        interpreter = _get_script_interpreter(script_file)
        if not interpreter:
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Cannot determine interpreter for: {script_path}"
                }],
                "success": False,
                "error": "unknown_interpreter"
            }

        # Build command
        cmd_parts = [interpreter, str(script_file)]
        if args:
            cmd_parts.extend(args)

        # Execute using the command executor
        command = " ".join(shlex.quote(part) for part in cmd_parts)
        return await execute_command(command, timeout, script_file.parent)

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Script execution failed: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def chain_commands(command_list: List[str], stop_on_error: bool = True) -> Dict[str, Any]:
    """
    Execute multiple commands in sequence.

    Args:
        command_list: List of commands to execute
        stop_on_error: Whether to stop on first error

    Returns:
        Dict with results from all commands
    """
    results = []
    success_count = 0
    failure_count = 0

    for i, command in enumerate(command_list):
        result = await execute_command(command)
        results.append({
            "command": command,
            "index": i,
            "result": result
        })

        if result.get("success"):
            success_count += 1
        else:
            failure_count += 1
            if stop_on_error:
                break

    summary = f"Command chain completed:\n"
    summary += f"✓ Success: {success_count}\n"
    summary += f"❌ Failed: {failure_count}\n"

    if stop_on_error and failure_count > 0:
        summary += f"\nStopped after first failure.\n"

    return {
        "content": [{
            "type": "text",
            "text": summary
        }],
        "success": failure_count == 0,
        "results": results,
        "success_count": success_count,
        "failure_count": failure_count
    }


def _validate_command(command: str) -> Dict[str, Union[bool, str]]:
    """Validate command for security."""
    # Get the base command (first word)
    base_command = command.strip().split()[0]

    # Check for restricted commands
    if base_command in RESTRICTED_COMMANDS:
        return {
            "safe": False,
            "reason": f"Command '{base_command}' is restricted for security"
        }

    # Check for obviously dangerous patterns
    dangerous_patterns = ["rm -rf", ":(){ :|:", "shutdown", "reboot", "format"]
    for pattern in dangerous_patterns:
        if pattern in command.lower():
            return {
                "safe": False,
                "reason": f"Command contains dangerous pattern: {pattern}"
            }

    # Check if command is in whitelist (if not in whitelist, allow but warn)
    if base_command not in ALLOWED_COMMANDS:
        return {
            "safe": True,
            "reason": f"Command '{base_command}' not in whitelist - proceed with caution"
        }

    return {"safe": True, "reason": "Command validated"}


def _get_script_interpreter(script_file: Path) -> Optional[str]:
    """Determine the appropriate interpreter for a script."""
    # Check shebang first
    try:
        with open(script_file, 'r') as f:
            first_line = f.readline().strip()
            if first_line.startswith('#!'):
                return first_line[2:].split()[0]
    except:
        pass

    # Determine by extension
    extension = script_file.suffix.lower()
    interpreters = {
        '.py': 'python3',
        '.js': 'node',
        '.ts': 'ts-node',
        '.rb': 'ruby',
        '.pl': 'perl',
        '.sh': 'bash',
        '.bash': 'bash',
        '.zsh': 'zsh',
        '.fish': 'fish'
    }

    return interpreters.get(extension)