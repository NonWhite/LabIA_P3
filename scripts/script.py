import os
from subprocess import call

SATPLAN = 'python ../code/satplan.py %s %s'
BLACKBOX = 'python ../code/blackbox.py %s %s'

if __name__ == "__main__" :
	dirs = [ '../data/blocks' , '../data/satellite' ]
	for d in dirs :
		files = [ ( d + '/' + f ) for f in os.listdir( d ) if f.endswith( '.in' ) ]
		files.sort()
		rulesfile = d + '/pddl.txt'
		for f in files :
			satplan = ( SATPLAN % ( rulesfile , f ) ).split()
			call( satplan )
			blackbox = ( BLACKBOX % ( rulesfile , f ) ).split()
			call( blackbox )
