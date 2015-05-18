import sys
from converter import *
from utils import *
from subprocess import call

VAR_DELIMITER = '_'

class StripsSolver :
	def __init__( self , stripsfile ) :
		self.domain = convertToJson( stripsfile )
		self.implications = []
		self.predicates = []
		self.actions = []
		self.var = {}
		self.steps = 0

	def getParameters( self , s ) :
		props = s.replace( '\n' , '' ).split( ';' )
		for i in range( len( props ) ) :
			name = self.searchInDomain( props[ i ] )[ 'name' ]
			lst = props[ i ][ len( name ) + 1 : ].split( '_' )
			props[ i ] = { 'name' : name , 'parameters' : lst }
		return props

	def getStartAndGoal( self , situationfile ) :
		self.init = self.goal = []
		with open( situationfile , 'r' ) as f :
			lines = f.readlines()
			self.start = self.getParameters( lines[ 0 ] )
			self.goal = self.getParameters( lines[ 1 ] )
	
	def searchInDomain( self , name ) :
		resp = {}
		match = ''
		for pred in self.domain[ 'predicates' ] :
			if name.startswith( pred[ 'name' ] ) :
				if len( pred[ 'name' ] ) > len( match ) :
					match = pred[ 'name' ]
					resp = pred
		return resp

	def addVariable( self , prop , variables , isAction = False , idvar = 0 ) :
		if idvar == len( prop[ 'parameters' ] ) : return [ prop ]
		lst = []
		( varname , typ ) = prop[ 'parameters' ][ idvar ]
		name = prop[ 'name' ]
		for value in variables[ typ ] :
			if value in name.split( VAR_DELIMITER ) : continue
			current = prop.copy()
			current[ 'name' ] += VAR_DELIMITER + value
			if isAction :
				for p in current[ 'precondition' ] :
					if varname not in p[ 'parameters' ] : continue
					p[ 'name' ] = p[ 'name' ].replace( '?' + varname , value )
					p[ 'parameters' ].remove( varname )
				for e in current[ 'effect' ] :
					if varname not in e[ 'parameters' ] : continue
					e[ 'name' ] = e[ 'name' ].replace( '?' + varname , value )
					e[ 'parameters' ].remove( varname )
			lst.extend( self.addVariable( current , variables , isAction , idvar + 1 ) )
		return lst

	def evaluateWith( self , prop , isAction = False , variables = None ) :
		if variables == None : variables = self.var
		if isAction :
			prop[ 'precondition' ] = prop[ 'precondition' ][ 'terms' ]
			prop[ 'effect' ] = prop[ 'effect' ][ 'terms' ]
			for pre in prop[ 'precondition' ] :
				for params in pre[ 'parameters' ] :
					pre[ 'name' ] += VAR_DELIMITER + '?' + params
			for ef in prop[ 'effect' ] :
				for params in ef[ 'parameters' ] :
					ef[ 'name' ] += VAR_DELIMITER + '?' + params
		lst = self.addVariable( prop , variables , isAction )
		if not isAction :
			for i in range( len( lst ) ) :
				lst[ i ] = lst[ i ][ 'name' ]
		else :
			for act in lst :
				keys = [ 'precondition' , 'effect' ]
				for k in keys :
					for x in act[ k ] : x.pop( 'parameters' , '' )
				act.pop( 'parameters' , '' )
		return lst

	def preprocess( self , situationfile ) :
		self.getStartAndGoal( situationfile )
		# Get how many variables has for each type (extracted from start and goal)
		for pred in self.start :
			name = pred[ 'name' ]
			params = pred[ 'parameters' ]
			obj = self.searchInDomain( name )
			for i in range( len( obj[ 'parameters' ] ) ) :
				typ = obj[ 'parameters' ][ i ][ 1 ]
				if typ not in self.var : self.var[ typ ] = []
				if params[ i ] not in self.var[ typ ] :
					self.var[ typ ].append( params[ i ] )
		for goal in self.goal :
			name = goal[ 'name' ]
			params = goal[ 'parameters' ]
			obj = self.searchInDomain( name )
			for i in range( len( obj[ 'parameters' ] ) ) :
				typ = obj[ 'parameters' ][ i ][ 1 ]
				if typ not in self.var : self.var[ typ ] = []
				if params[ i ] not in self.var[ typ ] :
					self.var[ typ ].append( params[ i ] )
		# Evaluate predicates with all variables detected
		for pred in self.domain[ 'predicates' ] :
			self.predicates.extend( self.evaluateWith( pred.copy() , isAction = False ) )
		# Evaluate actions with all variables detected
		for act in self.domain[ 'actions' ] :
			self.actions.extend( self.evaluateWith( act.copy() , isAction = True ) )
		# TODO
		for act in self.actions :
			act[ 'persistence' ] = []
		#print " ======== ACTIONS ======== "
		#for x in self.actions : print x
		# Get full description for start propositions
		for i in range( len( self.start ) ) :
			name = self.start[ i ][ 'name' ]
			for p in self.start[ i ][ 'parameters' ] :
				name += VAR_DELIMITER + p
			self.start[ i ] = { 'name' : name , 'state' : True }
		for pred in self.predicates :
			if pred not in getAllValues( self.start , 'name' ) :
				self.start.append( { 'name' : pred , 'state' : False } )
		for act in self.actions :
			for pre in getAllValues( act[ 'precondition' ] , 'name' ) :
				if pre not in getAllValues( self.start , 'name' ) :
					self.start.append( { 'name' : pre , 'state' : False } )
		#print " ======== START ======== "
		#for x in self.start : print x
		# Get full name for goal propositions
		for i in range( len( self.goal ) ) :
			name = self.goal[ i ][ 'name' ]
			for p in self.goal[ i ][ 'parameters' ] :
				name += VAR_DELIMITER + p
			self.goal[ i ] = { 'name' : name , 'state': True }
		#print " ======== GOAL ======== "
		#for x in self.goal : print x
		# Update list of predicates with not recognized propositions at init
		for p in getAllValues( self.start , 'name' ) :
			if p not in self.predicates : self.predicates.append( p )
		#print " ======== PREDICATES ======== "
		#for x in self.predicates : print x
		self.idpredicates = 1
		self.idactions = len( self.predicates ) + 1
		self.total = len( self.predicates ) + len( self.actions )

		print "#PREDICATES = %s" % len( self.predicates )
		print "#ACTIONS = %s" % len( self.actions )
		print "#IMPLICATIONS = %s" % len( self.implications )
		#print " ======== VAR ======== "
		#for ( typ , lstvars ) in self.var.iteritems() : print "%s: %s" % ( typ , lstvars )
	
	def getID( self , prop ) :
		if prop == None : return ''
		time = prop[ 'time' ]
		pos = 0
		if prop[ 'isaction' ] :
			pos = getAllValues( self.actions , 'name' ).index( prop[ 'name' ] )
			pos += self.idactions
		else :
			pos = self.predicates.index( prop[ 'name' ] )
			pos += self.idpredicates
		ID = pos + time * self.total
		if not prop[ 'state' ] : ID = -ID
		return ID

	# Convert propositions in CNF File
	def generateCNF( self ) :
		filename = "%s%s%s.out" % ( self.domain[ 'domain_name' ] , VAR_DELIMITER , self.steps )
		numvars = len( self.predicates ) + self.total * self.steps
		numclauses = len( self.implications ) + len( self.start ) + len( self.goal )
		f = open( filename , 'w' )
		print "Generating %s" % filename
		f.write( "p cnf %s %s\n" % ( numvars , numclauses ) )
		# Add start propositions
		for prop in self.start :
			if 'time' not in prop : prop[ 'time' ] = 0
			if 'isaction' not in prop : prop[ 'isaction' ] = False
			f.write( "%s 0\n" % self.getID( prop ) )
		# Add all axioms
		for imp in self.implications :
			left = imp[ 'left' ]
			right = imp[ 'right' ]
			factor = ( 1 if right == None else -1 )
			#f.write( "%s => %s\n" % ( left , right ) )
			for ifc in left :
				f.write( "%s " % ( factor * self.getID( ifc ) ) )
			f.write( "%s 0\n" % self.getID( right ) )
		# Add goal propositions
		for prop in self.goal :
			prop[ 'time' ] = self.steps
			prop[ 'isaction' ] = False
			f.write( "%s 0\n" % self.getID( prop ) )

		return filename
	
	# Process the CNF with SAT Solver
	def getStateFromCNF( self , cnffile ) :
		print "Solving %s" % cnffile
		satsolver = [ './toysat' , cnffile ]
		outfile = open( 'OUT' , 'w' )
		call( satsolver , stdout = outfile )
		return len( self.implications ) > 0

	# Return if current state is a solution
	def isSolved( self ) :
		cnffile = self.generateCNF()
		return self.getStateFromCNF( cnffile )
	
	def addAction( self ) :
		# Add axioms of preconditios
		for act in self.actions :
			left = [ formProposition( act[ 'name' ] , True , self.steps , True ) ]
			for pre in act[ 'precondition' ] :
				right = formProposition( pre[ 'name' ] , pre[ 'state' ] , self.steps , False )
				self.implications.append( { 'left' : left , 'right' : right } )
		# Add axioms of effect
		for act in self.actions :
			left = [ formProposition( act[ 'name' ] , True , self.steps , True ) ]
			for pre in act[ 'effect' ] :
				right = formProposition( pre[ 'name' ] , pre[ 'state' ] , self.steps + 1 , False )
				self.implications.append( { 'left' : left , 'right' : right } )
		# Add axioms of persistence
		for act in self.actions :
			for pers in act[ 'persistence' ] :
				left = [ formProposition( act[ 'name' ] , True , self.steps , True ) , \
							formProposition( pers[ 'name' ] , True , self.steps , False ) ]
				right = formProposition( pers[ 'name' ] , True , self.steps + 1 , False )
				self.implications.append( { 'left' : left , 'right' : right } )
		# Add axioms of continuity
		left = []
		for act in self.actions :
			left.append( formProposition( act[ 'name' ] , True , self.steps , True ) )
		right = None
		self.implications.append( { 'left' : left , 'right' : right } )
		# Add axioms of not paralelism
		for i in range( len( self.actions ) ) :
			left = [ formProposition( self.actions[ i ][ 'name' ] , True , self.steps , True ) ]
			for j in range( i + 1 , len( self.actions ) ) :
				right = formProposition( self.actions[ j ][ 'name' ] , False , self.steps , True )
				self.implications.append( { 'left' : left , 'right' : right } )

		self.steps += 1
		print "#IMPLICATIONS = %s" % len( self.implications )

	def process( self ) :
		while not self.isSolved() :
			self.addAction()
		return True

	def solve( self , situationfile ) :
		print "Pre-procesando informacion en %s" % situationfile
		self.preprocess( situationfile )
		return self.process()

if __name__ == "__main__" :
	if len( sys.argv ) == 3 :
		stripsfile = sys.argv[ 1 ]
		solver = StripsSolver( stripsfile )
		situationfile = sys.argv[ 2 ]
		solver.solve( situationfile )
	else :
		print 'Usage: %s [strips_filename] [scenary_filename]' % sys.argv[ 0 ]
