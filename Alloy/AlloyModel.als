////// Signatures
// Standard types
sig Float{}
sig string{}
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

// Company entity
one sig EnjoyCompany{
	stations: set SafeArea,
	cars: set Car,
}

// Current date for reservation
sig Date{}

// Car seservation
sig Reservation{
	driver: one Driver,
	car: one Car,
	date: one Date,
}

// Cancel car reservation
sig CancelReservation{
	reservation: one Reservation
}

// Car unlocked
sig Unlock{
	reservation: one Reservation
}

// Position for car, driver and parking area
sig Position{
	latitude: one Float,
	longitude: one Float
}

// The user of the system
sig Driver{
	//name: one string,
	//email: one string,
	//drivingLicense: one Int,
	//idCard : one Int,
	//credential: one Int,
	//password: one string,
	position: one Position,
	//rideInfo: lone Ride
}

// Cars provided by the system
sig Car{
	position: one Position,
	//batteryCharge: one Int,
	passengersNb: one Int,
	navigationScreen: one NavigationScreen,
	isLocked: one Bool,
	isParked: one Bool,
	isPlugged: one Bool,
	plug: lone Plug
}
{passengersNb < 5 and passengersNb > -1}
sig NavigationScreen{
	savingMoneyOption: one Bool,
	destination: lone Position
}

// Parking areas
sig SafeArea{
	position: one Position,
	places: one Int,
}
{places >0}
sig ChargingStation extends SafeArea{
	capacity: set Plug,
	chargingCars: set Car
}
{#chargingCars <= #capacity}
sig Plug{}


////// Facts
fact NoChargingCarInUse{
	no s: ChargingStation, r: Reservation | r.car.isLocked = False and  r.car not in s.chargingCars
}

fact NoCarsInSamePosition{
	no disj c1, c2: Car | c1.position = c2.position
}

fact NoSameReservation{
	no disj r1, r2: Reservation | r1.car = r2.car or r1.driver = r2.driver
}

fact NoSameCancel{
	no disj c1, c2: CancelReservation | c1.reservation = c2.reservation
}

fact NoSameUnlock{
	no disj u1,u2: Unlock | u1.reservation = u2.reservation
}

fact NoSameScreen{
	no disj c1, c2: Car | c1.navigationScreen = c2.navigationScreen
}

fact NoSceenWithoutCar{
	#NavigationScreen = #Car 
}

fact NoCarWithoutCompany{
	all c: Car | c in EnjoyCompany.cars
}

fact NoSafeAreaWithoutCompany{
	all s: SafeArea| s in EnjoyCompany.stations 
}

fact NoTwoSamePosition {
	no disj p1,p2: Position | p1.latitude = p2.latitude and p1.longitude = p2.longitude
}

fact CancelsReservation{
	all c: CancelReservation | c.reservation.car.isLocked = True and  c.reservation.car.isParked = True
}

fact NoPlugWithoutChargeStation{
	all p: Plug | p in ChargingStation.capacity 
}

fact NoPassengerIfNoReservation{
	all c: Car | !(c in Unlock.reservation.car) implies c.passengersNb=0
}

fact LockImpliesPark{
	all c: Car | c.isLocked = True implies c.isParked = True
}

fact NoCancelReservationAndUnlock{
	no r: Reservation | r in CancelReservation.reservation and r in Unlock.reservation
}

fact NoCarPlugInIfNoPlug{
	all c: Car | c.plug = none <=> c.isPlugged = False
}

fact NoSaveOptionIfLocked{
	all c: Car | c.isLocked = True implies c.navigationScreen.savingMoneyOption = False and  c.navigationScreen.destination=none
}

fact UnlockCar{
	all u: Unlock | u.reservation.driver.position = u.reservation.car.position 
}

fact  NoTwoCarsOnSamePlug {
	no disj c1: Car, c2: Car | c1 != c2 and c1.plug = c2.plug and c1.plug != none
}

fact NoCarLockIfDriverUnlocked {
	no u:Unlock | u.reservation.car.isLocked = True
}

fact NoCarUnlockedWithoutUnlock {
	no c: Car | !(c in Unlock.reservation.car) and c.isLocked = False
}

fact NoCarPluggedIfNotParked {
	no c: Car | c.isPlugged = True and c.isParked = False
}


////// Asserts
assert NoCarUnlockIfDriverCancelReservation {
	no c:CancelReservation | c.reservation.car.isLocked = False
}
//check NoCarUnlockIfDriverCancelReservation

assert NoDriverOrCarWithMultipleReservations {
	no disj r1,r2: Reservation | r1.driver = r2.driver or r1.car = r2.car
}
//check NoDriverOrCarWithMultipleReservations

assert AllCarsAndParkingAreasAttachedToEnjoyCompany {
	all c:Car | c in EnjoyCompany.cars and
	all sa:SafeArea | sa in EnjoyCompany.stations
}
//check AllCarsAndParkingAreasAttachedToEnjoyCompany

assert NoReservationCancelledAndUnlocked {
	no r: Reservation | r in Unlock.reservation and r in CancelReservation.reservation
}
//check NoReservationCancelledAndUnlocked

assert AllCarsLockedIfNoUnlock {
	no c: Car | !(c in Unlock.reservation.car) and c.isLocked = False
}
//check AllCarsLockedIfNoUnlock

assert NoSavingMoneyOptionIfCarLocked {
	no c: Car | c.isLocked = True and c.navigationScreen.savingMoneyOption = True
}
//check NoSavingMoneyOptionIfCarLocked

assert PassengersOnlyAfterUnlock{
	no c: Car | c.passengersNb > 0 and (c in CancelReservation.reservation.car or
																!(c in Reservation.car) or
																!(c in Unlock.reservation.car))
}
//check PassengersOnlyAfterUnlock


////// Predicates
pred show{
	#Driver = 2
	#SafeArea = 2
	#ChargingStation = 1
	#Reservation=2
	#Car= 2
	#Plug > 2
}
run show

