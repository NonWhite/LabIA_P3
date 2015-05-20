import os
from subprocess import call

if __name__ == "__main__" :
	#dirs = [ 'blocks' , 'satellite' ]
	dirs = [ 'satellite' ]
	for d in dirs :
		files = [ ( d + '/' + f ) for f in os.listdir( d ) if f.endswith( '.in' ) ]
		files.sort()
		rulesfile = d + '/pddl.txt'
		for f in files :
			solver = [ 'python' , 'solver.py' , rulesfile , f ]
			call( solver )
