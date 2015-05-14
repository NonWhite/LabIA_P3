import sys
from converter import *

def parseStripsFile( filename ) :
	js = convertToJson( filename )
	# TODO
	return js

if __name__ == "__main__" :
	if len( sys.argv ) == 2 :
		filename = sys.argv[ 1 ]
		parseStripsFile( filename )
