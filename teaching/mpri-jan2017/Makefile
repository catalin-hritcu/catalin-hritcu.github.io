dist:
	make -C slides
	rsync -av --progress . /home/hritcu/Inria/www-hritcu/teaching/mpri-jan2017 --exclude '*.exe' --exclude 'code/out' --exclude '*~' --delete
	cd /home/hritcu/Inria/www-hritcu; make
