
verify:
	make -C code/pure-fun
	make -C code/state
	make -C code/monotonic
	make -C code/effects
	make -C ex
	make -C sol

dist:
	make -C slides
	rsync -av --progress . /home/hritcu/Inria/www-hritcu/teaching/aarhus2017 --exclude '*.exe' --exclude 'code/out' --exclude '*~'
	cd /home/hritcu/Inria/www-hritcu; make
