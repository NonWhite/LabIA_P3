from default import *
import json as js
import re

# USELESS METHOD
def extractProps( line ) :
	line = line.replace( NEGATE_DELIMITER , '-_' )
	line = line.replace( '\n' , '' )
	props = line.split( PROPS_DELIMITER )
	lst = [ x.split( PARAMETERS_DELIMITER ) for x in props ]
	return lst

def extractMatches( pattern , s ) :
	lst = []
	while True :
		x = re.search( pattern , s )
		if x :
			lst.append( x.group( 0 ) )
			lastpos = x.end()
			s = s[ lastpos: ]
		else :
			break
	return lst

def convertToJson( filename ) :
	s = open( filename , 'r' ).read()
	for ( original , replaceable ) in REPLACEABLE_WORDS.iteritems() :
		s = s.replace( original , replaceable )
	lst = {}
	for ( pattern , key ) in EXTRACT_RULES.iteritems() :
		matches = extractMatches( pattern , s )
		lst[ key ] = curateFunctions[ key ]( matches )
	return lst

def parserStripsFile( filename ) :
	json = convertToJson( filename )
	otherfilename = filename.replace( 'txt' , 'json' )
	with open( otherfilename , 'w' ) as outfile :
		js.dump( json , outfile , indent = 4 , sort_keys = True )
	return json

if __name__ == "__main__" :
	f = 'b.txt'
	lst = parserStripsFile( f )
	print lst
	#for ( key , value ) in lst.iteritems() : print ( key , value )
