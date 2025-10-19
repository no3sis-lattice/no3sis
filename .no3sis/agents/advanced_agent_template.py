#!/usr/bin/env python3
# advanced_agent_claude_code_sdk.py

import asyncio
from typing import Any, AsyncGenerator, TypedDict

# --- Placeholder imports for the Claude Code SDK ---
# These would be the actual functions from "@anthropic-ai/claude-code"
from claude_code_sdk_placeholders import (
    create_sdk_mcp_server,
    tool,
    query,
    ClaudeCodeSdkMessage
)

# For styled console output
from rich.console import Console
from rich.panel import Panel

console = Console()

# --- 1. Type-Safe Schemas for Tools (NEW) ---
# Using TypedDict for type safety, similar to Zod in the documentation.
class WeatherToolArgs(TypedDict):
    location: str
    units: str # Can be "celsius" or "fahrenheit"

# --- 2. Tool Definition with Error Handling ---
@tool
async def get_weather(args: WeatherToolArgs) -> dict[str, Any]:
    """Gets the current weather for a specified location."""
    location = args.get("location")
    units = args.get("units", "celsius")
    
    console.print(f"[bold magenta]TOOL EXECUTED: get_weather(location='{location}', units='{units}')[/bold magenta]")
    
    # NEW: Added robust error handling as per best practices.
    try:
        if not location:
            raise ValueError("Location must be provided.")
        
        # In a real tool, you would call an external API here.
        # This is a mock response.
        weather_data = {"temperature": "15°C", "condition": "Partly Cloudy"}
        
        return {
            "content": [{
                "type": "text",
                "text": f"The weather in {location} is {weather_data['temperature']} and {weather_data['condition']}."
            }]
        }
    except Exception as e:
        console.print(f"[bold red]Error in get_weather tool: {e}[/bold red]")
        return {
            "content": [{
                "type": "text",
                "text": f"Sorry, I failed to get the weather. Error: {e}"
            }]
        }

# --- 3. Main Agent Logic ---

# NEW: Create an async generator for the prompt as required by MCP servers.
async def generate_prompt(user_message: str) -> AsyncGenerator[ClaudeCodeSdkMessage, None]:
    """Yields the user's prompt in the required streaming format."""
    yield {
        "type": "user",
        "message": {
            "role": "user",
            "content": user_message
        }
    }

async def main():
    """The main entry point for the agent application."""

    # 1. Create an MCP server to host our custom tool(s).
    weather_server = create_sdk_mcp_server(
        name="weather_tools",
        version="1.0.0",
        tools=[get_weather]
    )

    # 2. Define the user's prompt.
    # CONSIDERATION: This prompt explicitly invokes a subagent.
    # For this to work, you would need a file like .claude/agents/code-reviewer.md
    # user_prompt = "Use the code-reviewer subagent to check this file for bugs."
    user_prompt = "What's the weather like in Sunshine, Victoria?"
    
    console.print(Panel(user_prompt, title="User Prompt", border_style="yellow"))
    
    # 3. Query the agent using the streaming prompt format.
    # The client/query logic is now an async for loop.
    options = {
        "mcpServers": {
            "weather_tools": weather_server
        },
        "allowedTools": [
            "mcp__weather_tools__get_weather" # Format: mcp__{server_name}__{tool_name}
        ]
    }
    
    # NEW: The query now iterates over a streaming response.
    async for message in query(prompt=generate_prompt(user_prompt), options=options):
        if message.get("type") == "result" and message.get("subtype") == "success":
            # The final result from the agent after tool use.
            final_answer = message.get("result", {}).get("content", [{}])[0].get("text", "No text content found.")
            console.print(Panel(final_answer, title="Agent Response", border_style="green"))
        elif message.get("type") == "thought":
            # Optional: Print the agent's internal thoughts.
            console.print(f"[grey50]Thought: {message.get('thought')}[/grey50]")


# --- Application Entry Point ---
if __name__ == "__main__":
    # Note: You would need to install the actual Claude Code SDK for this to run.
    # pip install @anthropic-ai/claude-code-py (example package name)
    asyncio.run(main())
