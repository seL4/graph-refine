#!/bin/ksh

python ../../graph_to_graph.py ./ main --l -a rv64 2>&1 | tee l.log
python ../../graph_to_graph.py ./ main --L -a rv64 2>&1 | tee L.log

