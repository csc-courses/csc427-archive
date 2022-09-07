#
# use nbconvert to get python files from
# the code in jupyter notebook files
# author: bjr
# last-update:
#    03 apr 2021: created
#

F= `ls *.ipynb`

to-py:
	for i in $F ; do \
		echo "$$i" ; \
		jupyter nbconvert --to python --output-dir py "$$i" ; \
	done
