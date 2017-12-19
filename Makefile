
all: upload git

upload:
	rsync --delete -P -av --exclude=.git --exclude='*~' . hritcu@scm.gforge.inria.fr:/home/users/hritcu/htdocs/

git:
	-git commit -a -m "pre-distrib"

clean:
	rm -f *~
