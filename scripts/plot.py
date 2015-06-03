import os
import matplotlib.pyplot as plt
from copy import deepcopy as copy
from os.path import *

algorithms = [ 'satplan' , 'blackbox' ]
colors = [ 'b-' , 'r-' ] # Same length that algorithms

def doAndSavePlot( xticks , values , xlabel , ylabel , filename ) :
	plt.xticks( xticks[ 0 ] , xticks[ 1 ] , rotation = 90 )
	for i in range( len( values ) ) :
		data = values[ i ]
		plt.plot( data[ 0 ] , data[ 1 ] , colors[ i ] , linewidth = 2.0 )
	plt.xlabel( xlabel.capitalize() )
	plt.ylabel( ylabel.capitalize() )
	plt.savefig( filename )
	plt.clf()

def makePlots( directory ) :
	files = {}
	for alg in algorithms :
		files[ alg ] = [ directory + f for f in os.listdir( directory ) if f.endswith( '.out' ) and f.find( alg ) > 0 ]
	lstStats = {}
	stats = { 'name' : [] , 'time' : [] , 'props' : [] , 'clauses' : [] , 'size' : [] }
	# Merge all data for files
	for alg in algorithms :
		lstStats[ alg ] = copy( stats )
		for path in files[ alg ] :
			name = splitext( basename( path ) )[ 0 ].replace( '_' + alg , '' )
			lstStats[ alg ][ 'name' ].append( name )
			with open( path , 'r' ) as f :
				for line in f :
					if line.startswith( "SOLUTION" ) : break
					( key , value ) = line.split( " = " )
					lstStats[ alg ][ key.lower() ].append( float( value ) )
	# Make comparatives plots for every characteristic
	xlabel = 'Archivo'
	for key in stats :
		if key == 'name' : continue
		values = []
		xticks = []
		for alg in algorithms :
			length = len( lstStats[ alg ][ 'name' ] )
			if len( xticks ) == 0 :
				xticks = [ range( 1 , length + 1 ) , lstStats[ alg ][ 'name' ] ]
			values.append( [ range( 1 , length + 1 ) , lstStats[ alg ][ key ] ] )
		filename = "%s%s_%s.png" % ( directory , directory.split( '/' )[ -2 ] , key )
		doAndSavePlot( xticks , values , xlabel , key , filename )
	

if __name__ == "__main__" :
	directory = '/Users/nonwhite/Dropbox/IME/Laboratorio IA/LabIA_P3/data/blocks/'
	makePlots( directory )
	directory = '/Users/nonwhite/Dropbox/IME/Laboratorio IA/LabIA_P3/data/satellite/'
	makePlots( directory )
