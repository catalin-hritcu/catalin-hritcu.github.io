dist:
	make -C slides
	rsync -av --progress . /home/hritcu/Inria/www-hritcu/teaching/nancy2017 --exclude '*.exe' --exclude 'code/out' --exclude '*~' --delete
	cd /home/hritcu/Inria/www-hritcu; make
