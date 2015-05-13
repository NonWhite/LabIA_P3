import re

def test( regex , s = open( 'b.txt' ).read() ) :
	x = re.search( regex , s )
	if x :
		print x.group( 0 )
	else :
		print 'not found'
