import sys
from converter import *

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

	def preprocess( self , situationfile ) :
		self.getStartAndGoal( situationfile )
		# Get how many variables has for each type
		self.var = {}
		print " ======== PREDICATES ======== "
		for x in self.domain[ 'predicates' ] : print x
		print " ======== START ======== "
		for x in self.start : print x
		print " ======== GOAL ======== "
		for x in self.goal : print x
		for pred in self.start :
			name = pred[ 'name' ]
			params = pred[ 'parameters' ]
			obj = self.searchInDomain( name )
			for i in range( len( obj[ 'parameters' ] ) ) :
				typ = obj[ 'parameters' ][ i ][ 1 ]
				if typ not in self.var : self.var[ typ ] = []
				if params[ i ] not in self.var[ typ ] :
					self.var[ typ ].append( params[ i ] )
		print self.var
		return 'preprocess'

	def solve( self , situationfile ) :
		print "Pre-procesando informacion en %s" % situationfile
		self.preprocess( situationfile )
		# TODO
		return 'solve'

if __name__ == "__main__" :
	if len( sys.argv ) == 3 :
		stripsfile = sys.argv[ 1 ]
		solver = StripsSolver( stripsfile )
		situationfile = sys.argv[ 2 ]
		solver.solve( situationfile )
