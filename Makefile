
distrib:
	git commit -a -m "pre-distrib"
	rsync -av --delete --filter='exclude .git' . hritcu@scm.gforge.inria.fr:/home/users/hritcu/htdocs/

clean:
	rm -f *~
