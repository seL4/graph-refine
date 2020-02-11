#!/bin/ksh

python ../../graph_to_graph.py ./ main --x -a rv64 2>&1 | tee x.log
#python ../../graph_to_graph.py ./ main --L -a rv64 2>&1 | tee L.log

