
distrib:
	git commit -a -m "pre-distrib"
	rsync -av --delete --exclude=.git --exclude=Makefile --exclude='*~' . hritcu@scm.gforge.inria.fr:/home/users/hritcu/htdocs/

clean:
	rm -f *~
