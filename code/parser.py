from default import *
import json

# USELESS METHOD
def extractProps( line ) :
	line = line.replace( NEGATE_DELIMITER , '-_' )
	line = line.replace( '\n' , '' )
	props = line.split( PROPS_DELIMITER )
	lst = [ x.split( PARAMETERS_DELIMITER ) for x in props ]
	return lst

def parserStripsFile( filename ) :
	f = open( filename , 'r' )
	x = f.read()
	x = x.replace( '(' , '{' )
	x = x.replace( ')' , '}' )
	outfile = open( 'e.json' , 'w' )
	json.dump( x , outfile )
	return 'AC'

if __name__ == "__main__" :
	f = 'test.in'
	print parserStripsFile( f )
