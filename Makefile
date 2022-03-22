all:
	tidy -i index.html > index.tmp
	mv index.tmp index.html

	tidy -i publications.html > publications.tmp
	mv publications.tmp publications.html

	tidy -i teaching/index.html > teaching/index.tmp
	mv teaching/index.tmp teaching/index.html

	tidy -i teaching/ST22/index.html > teaching/ST22/index.tmp
	mv teaching/ST22/index.tmp teaching/ST22/index.html










