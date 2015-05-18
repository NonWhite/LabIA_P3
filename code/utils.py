def getAllValues( lstDictionary , key ) :
	lst = []
	for x in lstDictionary : lst.append( x[ key ] )
	return lst

def formProposition( name , state , time , isaction ) :
	return { 'name' : name , 'state' : state , 'time' : time , 'isaction' : isaction }
