import os
from subprocess import call

if __name__ == "__main__" :
	dirs = [ '../data/blocks' , '../data/satellite' ]
	for d in dirs :
		files = [ ( d + '/' + f ) for f in os.listdir( d ) if f.endswith( '.in' ) ]
		files.sort()
		rulesfile = d + '/pddl.txt'
		for f in files :
			satplan = [ 'python' , '../code/satplan.py' , rulesfile , f ]
			call( satplan )
