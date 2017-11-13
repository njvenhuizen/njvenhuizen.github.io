all:
	/opt/local/bin/tidy -i index.html > index.tmp
	mv index.tmp index.html

	/opt/local/bin/tidy -i publications.html > publications.tmp
	mv publications.tmp publications.html

	/opt/local/bin/tidy -i teaching/index.html > teaching/index.tmp
	mv teaching/index.tmp teaching/index.html
