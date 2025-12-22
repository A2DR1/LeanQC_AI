#!/usr/bin/env bash
set -e

echo "🧹 Cleaning history folders..."

# Safety check
if [ ! -d "history" ]; then
  echo "❌ history/ directory not found. Aborting."
  exit 1
fi

# Clear contents of history subfolders
for dir in history/CNL history/Lean_files history/NL_FL_pairs; do
  if [ -d "$dir" ]; then
    echo "  → Clearing $dir"
    rm -rf "$dir"/*
  else
    echo "  ⚠️  $dir does not exist, skipping."
  fi
done

echo "🧹 Removing cnl_statements_v*.json in project root..."
rm -f cnl_statements_v*.json

echo "✅ Cleanup complete. Fresh state ready."