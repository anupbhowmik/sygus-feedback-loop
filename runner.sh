#!/bin/bash

# Check if new-problems directory exists
if [ ! -d "new-problems" ]; then
    echo "Error: new-problems directory not found"
    exit 1
fi

# Loop through each file in new-problems directory
for file in new-problems/*; do
    # Check if any files exist
    if [ ! -e "$file" ]; then
        echo "No files found in new-problems directory"
        break
    fi
    
    # Skip if it's a directory
    if [ -d "$file" ]; then
        continue
    fi
    
    # Extract filename without extension for output directory
    filename=$(basename "$file")
    filename_no_ext="${filename%.*}"
    
    echo "Processing: $file"
    
    # Create output directory if it doesn't exist
    mkdir -p "tmp/$filename_no_ext"
    
    # Run the command
    python llm_loop.py -p "$file" -v -t 10 > "logs/$filename_no_ext/output.log" 2>&1
    
    echo "Completed: $file"
    echo "---"
done

echo "All files processed"