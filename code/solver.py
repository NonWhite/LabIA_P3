import sys
from converter import *

VAR_DELIMITER = '_'

class StripsSolver :
	def __init__( self , stripsfile ) :
		self.domain = convertToJson( stripsfile )

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

	def addVariableToAction( self , action , variables , idvar = 0 ) :
		if idvar == len( action[ 'parameters' ] ) : return [ action ]
		lst = []
		( varname , typ ) = action[ 'parameters' ][ idvar ]
		name = action[ 'name' ]
		for value in variables[ typ ] :
			if value in name.split( VAR_DELIMITER ) : continue
			current = action.copy()
			current[ 'name' ] += VAR_DELIMITER + value
			for p in current[ 'precondition' ][ 'terms' ] :
				if varname not in p[ 'parameters' ] : continue
				p[ 'name' ] += VAR_DELIMITER + value
				p[ 'parameters' ].remove( varname )
			for e in current[ 'effect' ][ 'terms' ] :
				if varname not in e[ 'parameters' ] : continue
				e[ 'name' ] += VAR_DELIMITER + value
				e[ 'parameters' ].remove( varname )
			lst.extend( self.addVariableToAction( current , variables , idvar + 1 ) )
		return lst

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
				for p in current[ 'precondition' ][ 'terms' ] :
					if varname not in p[ 'parameters' ] : continue
					p[ 'name' ] += VAR_DELIMITER + value
					p[ 'parameters' ].remove( varname )
				for e in current[ 'effect' ][ 'terms' ] :
					if varname not in e[ 'parameters' ] : continue
					e[ 'name' ] += VAR_DELIMITER + value
					e[ 'parameters' ].remove( varname )
			lst.extend( self.addVariable( current , variables , isAction , idvar + 1 ) )
		return lst

	def evaluateWith( self , prop , isAction = False , variables = None ) :
		if variables == None : variables = self.var
		lst = self.addVariable( prop , variables , isAction )
		if not isAction :
			for i in range( len( lst ) ) : lst[ i ] = { 'name' : lst[ i ][ 'name' ] , 'state' : True }
		else :
			for act in lst :
				keys = [ 'precondition' , 'effect' ]
				for k in keys :
					act[ k ] = act[ k ][ 'terms' ]
					for x in act[ k ] : x.pop( 'parameters' , '' )
				act.pop( 'parameters' , '' )
		return lst

	def preprocess( self , situationfile ) :
		self.getStartAndGoal( situationfile )
		# Get how many variables has for each type
		self.var = {}
		for pred in self.start :
			name = pred[ 'name' ]
			params = pred[ 'parameters' ]
			obj = self.searchInDomain( name )
			for i in range( len( obj[ 'parameters' ] ) ) :
				typ = obj[ 'parameters' ][ i ][ 1 ]
				if typ not in self.var : self.var[ typ ] = []
				if params[ i ] not in self.var[ typ ] :
					self.var[ typ ].append( params[ i ] )
		self.predicates = []
		for pred in self.domain[ 'predicates' ] :
			self.predicates.extend( self.evaluateWith( pred.copy() , isAction = False ) )
		print self.predicates
		self.actions = []
		for act in self.domain[ 'actions' ] :
			self.actions.extend( self.evaluateWith( act.copy() , isAction = True ) )
			break
		print self.actions
		#print self.actions
		#print " ======== START ======== "
		#for x in self.start : print x
		#print " ======== GOAL ======== "
		#for x in self.goal : print x
		#print " ======== PREDICATES ======== "
		#for x in self.domain[ 'predicates' ] : print x
		#print " ======== ACTIONS ======== "
		#for x in self.domain[ 'actions' ] : print x
		#print " ======== VAR ======== "
		#for ( typ , lstvars ) in self.var.iteritems() : print "%s: %s" % ( typ , lstvars )
		#self.initialize()
		return 'preprocess'

	# TODO: Create initial structure of propositions with self.start
	def initialize( self ) :
		return 'me'

	# TODO Convert propositions in CNF File
	def generateCNF( self ) :
		return 'cnf'
	
	# TODO Process the CNF with SAT Solver
	def getStateFromCNF( self , cnffile ) :
		return True

	# TODO Return if current state is a solution
	def isSolved( self ) :
		cnffile = self.generateCNF()
		return self.getStateFromCNF( cnffile )
	
	def addAction( self ) :
		return 'action'

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
