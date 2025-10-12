#!/bin/bash
cd Duality/Chunks
for i in $(seq -w 1 62); do
  if [ -f "chunk-${i}.lean" ]; then
    mv "chunk-${i}.lean" "Chunk${i}.lean"
  fi
done
