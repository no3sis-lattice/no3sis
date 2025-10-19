"""
Process Management Tools

Tools for monitoring and controlling processes.
"""

import os
import psutil
import asyncio
import signal
from typing import Dict, Any, List, Optional
from datetime import datetime


async def check_status(process_id: int) -> Dict[str, Any]:
    """
    Check the status of a process by PID.

    Args:
        process_id: Process ID to check

    Returns:
        Dict with process status information
    """
    try:
        if not psutil.pid_exists(process_id):
            return {
                "content": [{
                    "type": "text",
                    "text": f"Process {process_id} does not exist"
                }],
                "exists": False,
                "pid": process_id
            }

        process = psutil.Process(process_id)

        # Gather process information
        info = {
            "pid": process_id,
            "name": process.name(),
            "status": process.status(),
            "cpu_percent": process.cpu_percent(),
            "memory_percent": process.memory_percent(),
            "create_time": datetime.fromtimestamp(process.create_time()).isoformat(),
            "cmdline": " ".join(process.cmdline()) if process.cmdline() else "N/A"
        }

        # Try to get additional info (may fail for some processes)
        try:
            info["username"] = process.username()
            info["cwd"] = process.cwd()
            info["num_threads"] = process.num_threads()
        except (psutil.AccessDenied, psutil.NoSuchProcess):
            pass

        status_text = f"Process {process_id} status:\n"
        status_text += f"Name: {info['name']}\n"
        status_text += f"Status: {info['status']}\n"
        status_text += f"CPU: {info['cpu_percent']:.1f}%\n"
        status_text += f"Memory: {info['memory_percent']:.1f}%\n"
        status_text += f"Command: {info['cmdline']}\n"

        return {
            "content": [{
                "type": "text",
                "text": status_text
            }],
            "exists": True,
            "process_info": info
        }

    except psutil.NoSuchProcess:
        return {
            "content": [{
                "type": "text",
                "text": f"Process {process_id} no longer exists"
            }],
            "exists": False,
            "pid": process_id
        }
    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"Error checking process {process_id}: {str(e)}"
            }],
            "error": str(e)
        }


async def kill_process(process_id: int, force: bool = False) -> Dict[str, Any]:
    """
    Terminate a process by PID.

    Args:
        process_id: Process ID to terminate
        force: Use SIGKILL instead of SIGTERM

    Returns:
        Dict with termination status
    """
    try:
        if not psutil.pid_exists(process_id):
            return {
                "content": [{
                    "type": "text",
                    "text": f"Process {process_id} does not exist"
                }],
                "success": False,
                "reason": "process_not_found"
            }

        process = psutil.Process(process_id)
        process_name = process.name()

        # Security check - don't kill critical system processes
        critical_processes = {"init", "kernel", "systemd", "kthreadd"}
        if process_name.lower() in critical_processes:
            return {
                "content": [{
                    "type": "text",
                    "text": f"❌ Cannot kill critical system process: {process_name}"
                }],
                "success": False,
                "reason": "critical_process"
            }

        # Attempt termination
        if force:
            process.kill()  # SIGKILL
            action = "killed (SIGKILL)"
        else:
            process.terminate()  # SIGTERM
            action = "terminated (SIGTERM)"

        # Wait for process to actually terminate
        try:
            process.wait(timeout=5)
            terminated = True
        except psutil.TimeoutExpired:
            terminated = False

        result_text = f"Process {process_id} ({process_name}) {action}"
        if not terminated:
            result_text += " (may still be running)"

        return {
            "content": [{
                "type": "text",
                "text": result_text
            }],
            "success": terminated,
            "pid": process_id,
            "process_name": process_name,
            "force": force,
            "terminated": terminated
        }

    except psutil.NoSuchProcess:
        return {
            "content": [{
                "type": "text",
                "text": f"Process {process_id} no longer exists"
            }],
            "success": True,  # Process is gone, goal achieved
            "reason": "already_gone"
        }
    except psutil.AccessDenied:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Access denied: Cannot terminate process {process_id}"
            }],
            "success": False,
            "reason": "access_denied"
        }
    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Error terminating process {process_id}: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }


async def list_processes(filter_name: Optional[str] = None, limit: int = 20) -> Dict[str, Any]:
    """
    List running processes with optional filtering.

    Args:
        filter_name: Filter processes by name (partial match)
        limit: Maximum number of processes to return

    Returns:
        Dict with process list
    """
    try:
        processes = []

        for proc in psutil.process_iter(['pid', 'name', 'cpu_percent', 'memory_percent', 'status']):
            try:
                pinfo = proc.info

                # Apply name filter if specified
                if filter_name and filter_name.lower() not in pinfo['name'].lower():
                    continue

                processes.append({
                    'pid': pinfo['pid'],
                    'name': pinfo['name'],
                    'cpu_percent': pinfo['cpu_percent'] or 0,
                    'memory_percent': pinfo['memory_percent'] or 0,
                    'status': pinfo['status']
                })

            except (psutil.NoSuchProcess, psutil.AccessDenied):
                # Process disappeared or access denied, skip it
                continue

        # Sort by CPU usage (descending) and limit results
        processes.sort(key=lambda x: x['cpu_percent'], reverse=True)
        processes = processes[:limit]

        # Format output
        if not processes:
            result_text = "No processes found"
            if filter_name:
                result_text += f" matching '{filter_name}'"
        else:
            result_text = f"Processes ({len(processes)} shown"
            if filter_name:
                result_text += f", filtered by '{filter_name}'"
            result_text += "):\n\n"

            result_text += f"{'PID':<8} {'Name':<20} {'CPU%':<8} {'Mem%':<8} {'Status'}\n"
            result_text += "-" * 60 + "\n"

            for proc in processes:
                result_text += f"{proc['pid']:<8} {proc['name'][:19]:<20} "
                result_text += f"{proc['cpu_percent']:<7.1f} {proc['memory_percent']:<7.1f} "
                result_text += f"{proc['status']}\n"

        return {
            "content": [{
                "type": "text",
                "text": result_text
            }],
            "success": True,
            "processes": processes,
            "count": len(processes),
            "filter_applied": filter_name
        }

    except Exception as e:
        return {
            "content": [{
                "type": "text",
                "text": f"❌ Error listing processes: {str(e)}"
            }],
            "success": False,
            "error": str(e)
        }