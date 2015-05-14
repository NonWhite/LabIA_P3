from extractor import *
import os
import json
import re

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
	newname = os.path.splitext( filename )[ 0 ] + '.json'
	with open( newname , 'w' ) as jsonfile :
		json.dump( lst , jsonfile , indent = 4 , sort_keys = True )
	return lst

if __name__ == "__main__" :
	print 'converter'
