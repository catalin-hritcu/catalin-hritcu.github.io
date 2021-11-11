dist:
	make -C slides
	rsync -av --progress . /home/hritcu/Inria/www-hritcu/teaching/bucharest-school-2016 --exclude '*.exe' --exclude 'code/out' --exclude '*~' --delete
	cd /home/hritcu/Inria/www-hritcu; make
