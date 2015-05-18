import re

NEGATE_DELIMITER = '~'
PARAMETERS_DELIMITER = '_'
PROPS_DELIMITER = ';'

EXTRACT_RULES = {
	'define(.*)\(.*\)' : 'domain_name' ,
	'\(.*requirements.*\)' : 'requirements' ,
	'\(.*types.*\)' : 'types' ,
	'\(.*predicates(.|\n)[^:]*\)' : 'predicates' ,
	'\(.*action(.|\n)[^:]*\)' : 'actions'
}

REPLACEABLE_WORDS = {
	':parameters' : 'parameters' ,
	':precondition' : 'precondition' ,
	':effect' : 'effect'
}

# ---------- DOMAIN NAME -----------------
def extractDomainName( lst ) :
	resp = re.search( '[^\(].*domain.*[^\)]' , lst[ 0 ] ).group( 0 )
	removable = [ 'domain' , '(' , ')' , 'define' ]
	for s in removable : resp = resp.replace( s , '' ).strip()
	return resp

# ---------- REQUIREMENTS -----------------
def extractRequirements( lst ) :
	resp = re.search( '[^\(].*requirements.*[^\)]' , lst[ 0 ] ).group( 0 ).replace( 'domain' , '' ).strip()
	resp = resp.split( ' ' )[ 1: ]
	return resp

# ---------- TYPES -----------------
def extractTypes( lst ) :
	resp = re.search( '[^\(].*types.*[^\)]' , lst[ 0 ] ).group( 0 ).strip()
	resp = resp.split( ' ' )[ 1: ]
	return resp

# ---------- PREDICATES -----------------
def parsePredicateString( s ) :
	lst = s.strip()[ 1:-1 ].strip().split( '?' )
	resp = {}
	resp[ 'name' ] = lst[ 0 ].strip()
	resp[ 'parameters' ] = [ r.strip().split( ' - ' ) for r in lst[ 1: ] ]
	return resp

def extractPredicates( lst ) :
	resp = lst[ 0 ].strip()
	removable = [ ':predicates' , '\t' , '\r' ]
	for s in removable : resp = resp.replace( s , '' )
	resp = resp[ 1:-1 ].strip()
	resp = resp.split( '\n' )
	for i in range( len( resp ) ) : resp[ i ] = parsePredicateString( resp[ i ] )
	return resp

# ---------- ACTIONS -----------------
def parseString( s ) :
	state = True
	s = s.strip()[ 1:-1 ].strip()
	if s.startswith( 'not' ) :
		state = False
		s = s.replace( 'not' , '' ).strip()[ 1:-1 ]
	lst = s.split( '?' )
	resp = {}
	resp[ 'name' ] = lst[ 0 ].strip()
	resp[ 'parameters' ] = [ x.strip() for x in lst[ 1: ] ]
	resp[ 'state' ] = state
	return resp
	

def parseInformation( s , regex ) :
	removable = [ '\t' , '\r' , 'precondition' , ':effect' ]
	resp = re.search( regex , s ).group( 0 ).strip()
	for s in removable : resp = resp.replace( s , '' ).strip()
	resp = [ x.strip() for x in resp.split( '\n' ) ]
	if resp[ 0 ].find( 'and ' ) >= 0 :
		resp[ 0 ] = resp[ 0 ].replace( '(and' , '' ).replace( '( and' , '' )
		resp.insert( 0 , '( and' )
	while resp[ len( resp ) - 1 ].strip() == ')' : resp.pop( len( resp ) - 1 )
	if len( resp ) == 1 :
		resp = { 'prop' : 'none' , 'terms' : [ parseString( resp[ 0 ] ) ] }
	else :
		resp.append( ')' )
		resp = { 'prop' : resp[ 0 ].replace( '(' , '' ).replace( ' ' , '' ) , 'terms' : [ parseString( x ) for x in resp[ 1:-1 ] ] }
	return resp

def extractActions( lst ) :
	resp = []
	for act in lst :
		act = act.strip()[ 1:-1 ].replace( ':action' , '' ).replace( 'effect' , ':effect' ).strip()
		name = re.search( '.*\n' , act ).group( 0 ).replace( '\n' , '' ).replace( '\r' , '' )
		parameters = re.search( '.*parameters.*\(.*\)' , act ).group( 0 ).replace( '\t' , '' ).replace( 'parameters' , '' ).strip()[ 1:-1 ].strip()
		parameters = [ r.split( ' - ' ) for r in parameters.split( '?' )[ 1: ] ]
		parameters = [ [ r[ 0 ].strip() , r[ 1 ].strip() ] for r in parameters ]
		precondition = parseInformation( act , '.*precondition(.|\n)[^:]*\)' )
		effect = parseInformation( act , '.*effect(.|\n)*\)' )
		dictAct = { 'name' : name , 'parameters': parameters , 'precondition' : precondition , 'effect' : effect }
		resp.append( dictAct )
	return resp

curateFunctions = {
	'domain_name' : extractDomainName ,
	'requirements' : extractRequirements ,
	'types' : extractTypes ,
	'predicates' : extractPredicates ,
	'actions' : extractActions
}
