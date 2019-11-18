for v in 4; do
    for k in {1..25}; do
	for h in {1..3}; do
	    echo "${v} ${k} ${h}"
	    for i in {0..9}; do
		python3 bench.py benchmarks/synthetics_${v}_${v}_${k}_3_${h}_${i}.smt2 1000 42;
	    done
       	done
    done
done
