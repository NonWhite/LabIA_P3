import os

if __name__ == "__main__" :
	files = [ w for w in os.listdir( '.' ) if w.startswith( 'blocks' ) ]
	for name in files :
		newname = name.replace( '.strips' , '.in' )
		newlines = []
		with open( name , 'r' ) as f :
			lines = [ w.strip() for w in f.readlines() ]
			pos = lines.index( '' )
			newlines = lines[ (pos+1): ]
		with open( newname , 'w' ) as f :
			for line in newlines :
				f.write( "%s\n" % line )
