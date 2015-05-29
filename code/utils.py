def getAllValues( lstDictionary , key ) :
	lst = []
	for x in lstDictionary : lst.append( x[ key ] )
	return lst

def formProposition( name , state , time , isaction ) :
	return { 'name' : name , 'state' : state , 'time' : time , 'isaction' : isaction }

def isnumber( s ) :
	return s[ 1: ].isdigit() if s.startswith( '-' ) else s.isdigit()
